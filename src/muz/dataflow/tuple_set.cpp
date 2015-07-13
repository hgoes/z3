#include "tuple_set.h"

namespace datalog {

    const tuple_set tuple_set::null_fact = tuple_set();

    bool tuple_set::insert_fact(ctx_t& ctx, svector<expr*>& fact_buffer, unsigned fact_offset) {
        if (m_num_cols == 0) {
            if (!has_tuples) {
                has_tuples = true;
                return true;
            } else {
                return false;
            }
        }
        // Check if the fact already exists
        for (unsigned i = 0; i < m_num_rows; ++i) {
            bool equal = true;
            for (unsigned j = 0; j < m_num_cols; ++j) {
                if (m_tuples[i*m_num_cols + j] != fact_buffer[fact_offset + j]) {
                    // Tuple is different
                    equal = false;
                    break;
                }
            }
            if (equal) {
                //std::cout << "Fact already exists." << std::endl;
                return false;
            }
        }
        // The fact doesn't yet exist
        m_tuples.resize((m_num_rows + 1)*m_num_cols);
        for (unsigned i = 0; i < m_num_cols; ++i) {
            m_tuples[m_num_rows*m_num_cols + i] = fact_buffer[fact_offset + i];
        }
        ++m_num_rows;
        has_tuples = true;
        //std::cout << "Inserted new fact (" << m_num_cols << " cols, " << m_num_rows << " rows)." << std::endl;
        return true;
    }

    bool tuple_set::deduce_var_facts(tuple_set_ctx& ctx, rule* r, const fact_reader<tuple_set>& facts) {
        SASSERT(m_num_cols == m_indices.size());
        SASSERT(m_tuples.size() == m_num_cols*m_num_rows);
        unsigned_vector& iter = ctx.m_iter;
        svector<const tuple_set*>& tail_facts = ctx.m_tail_facts;
        svector<expr*>& buffer = ctx.m_buffer;
        const unsigned utail_size = r->get_positive_tail_size();
        iter.resize(utail_size);
        tail_facts.resize(utail_size);
        unsigned max_vidx = 0;
        app* head = r->get_head();
        for (unsigned i = 0; i < head->get_num_args(); ++i) {
            expr* arg = head->get_arg(i);
            if (is_var(arg)) {
                const unsigned vidx = to_var(arg)->get_idx();
                if (max_vidx < vidx) {
                    max_vidx = vidx;
                }
            }
        }
        for (unsigned i = 0; i < utail_size; ++i) {
            app* el = r->get_tail(i);
            const tuple_set& fact = facts.get(i);
            tail_facts[i] = &fact;
            iter[i] = 0;
            // Make the buffer large enough for all var indices
            for (unsigned j = 0; j < el->get_num_args(); ++j) {
                expr* arg = el->get_arg(j);
                if (is_var(arg)) {
                    const unsigned vidx = to_var(arg)->get_idx();
                    if (max_vidx < vidx) {
                        max_vidx = vidx;
                    }
                }
            }
        }
        for (unsigned i = utail_size; i < r->get_tail_size(); ++i) {
            app* el = r->get_tail(i);
            // Make the buffer large enough for all var indices
            for (unsigned j = 0; j < el->get_num_args(); ++j) {
                expr* arg = el->get_arg(j);
                if (is_var(arg)) {
                    const unsigned vidx = to_var(arg)->get_idx();
                    if (max_vidx < vidx) {
                        max_vidx = vidx;
                    }
                }
            }
        }
        buffer.resize(max_vidx + 1, 0);
        bool new_facts = false;
        bool valid_iter = true;
        while (valid_iter) {
            bool feasible = true;
            buffer.fill(0);
            for (unsigned i = 0; i < utail_size; ++i) {
                app* el = r->get_tail(i);
                const tuple_set* fact = tail_facts[i];
                const unsigned fact_nr = iter[i];
                const unsigned num_cols = fact->num_cols();
                const unsigned num_rows = fact->num_rows();
                if (num_rows == 0 && num_cols != 0)
                    continue;
                for (unsigned j = 0; j < num_cols; ++j) {
                    const unsigned arg_idx = fact->m_indices[j];
                    expr* arg = el->get_arg(arg_idx);
                    if (is_var(arg)) {
                        const unsigned vidx = to_var(arg)->get_idx();
                        if (buffer[vidx] == 0) {
                            // The variable is not yet assigned, assign it
                            buffer[vidx] = fact->m_tuples[fact_nr*num_cols + j];
                        } else {
                            if (buffer[vidx] != fact->m_tuples[fact_nr*num_cols + j]) {
                                // The variable was assigned and conflicts with the current tuple
                                feasible = false;
                                break;
                            }
                        }
                    } else {
                        if (arg != fact->m_tuples[fact_nr*num_cols + j]) {
                            // The constant conflicts with the current tuple
                            feasible = false;
                            break;
                        }
                    }
                }
                if (!feasible) {
                    //std::cout << "Infeasible tuple." << std::endl;
                    break;
                }
            }
            if (feasible) {
                // Process equalities in the interpreted tail
                for (unsigned j = r->get_uninterpreted_tail_size(); j < r->get_tail_size(); ++j) {
                    app *elem = r->get_tail(j);
                    if (ctx.m.is_eq(elem) && !r->is_neg_tail(j)) {
                        expr *lhs = elem->get_arg(0);
                        expr *rhs = elem->get_arg(1);
                        if (is_var(lhs)) {
                            const unsigned l_idx = to_var(lhs)->get_idx();
                            if (is_var(rhs)) {
                                const unsigned r_idx = to_var(rhs)->get_idx();
                                if (buffer[l_idx]) {
                                    if (buffer[r_idx]) {
                                        if (buffer[l_idx] != buffer[r_idx]) {
                                            feasible = false;
                                            break;
                                        }
                                    } else {
                                        buffer[r_idx] = buffer[l_idx];
                                    }
                                } else {
                                    if (buffer[r_idx]) {
                                        buffer[l_idx] = buffer[r_idx];
                                    }
                                }
                            } else if (ctx.m.is_value(rhs)) {
                                if (buffer[l_idx]) {
                                    if (buffer[l_idx] != rhs) {
                                        feasible = false;
                                        break;
                                    }
                                } else {
                                    buffer[l_idx] = rhs;
                                }
                            }
                        } else if(ctx.m.is_value(lhs)) {
                            if (is_var(rhs)) {
                                const unsigned r_idx = to_var(rhs)->get_idx();
                                if (buffer[r_idx]) {
                                    if (buffer[r_idx] != lhs) {
                                        feasible = false;
                                        break;
                                    }
                                } else {
                                    buffer[r_idx] = lhs;
                                }
                            }
                        }
                    }
                }
            }
            if (feasible) {
                const unsigned buf_size = buffer.size();
                // Write the new fact to the end of the buffer
                buffer.resize(buf_size + m_num_cols);
                unsigned j = 0;
                while(j < m_num_cols) {
                    const unsigned idx = m_indices[j];
                    expr* arg = r->get_head()->get_arg(idx);
                    if (is_var(arg)) {
                        const unsigned vidx = to_var(arg)->get_idx();
                        if (buffer[vidx] == 0) {
                            // The argument is unbounded
                            delete_column(j);
                            remove_duplicates();
                            new_facts = true;
                            //m_num_cols--;
                        } else {
                            buffer[buf_size + j] = buffer[vidx];
                            ++j;
                        }
                    } else {
                        buffer[buf_size + j] = arg;
                        ++j;
                    }
                }
                if (insert_fact(ctx, buffer, buf_size)) {
                    //++nrows;
                    new_facts = true;
                }
            }
            // Increment the iterators
            valid_iter = false;
            for (unsigned i = 0; i < iter.size(); ++i) {
                if (++iter[i] >= tail_facts[i]->m_num_rows) {
                    iter[i] = 0;
                } else {
                    valid_iter = true;
                    break;
                }
            }
        }
        if (new_facts) {
            prune(ctx);
        }
        //std::cout << (new_facts ? "NEW" : "OLD") << " facts." << std::endl;
        return new_facts;
    }
    bool tuple_set::deduce_base_facts(tuple_set_ctx& ctx, const rule* r) {
        SASSERT(m_num_cols == m_indices.size());
        SASSERT(m_tuples.size() == m_num_cols*m_num_rows);
        //std::cout << "Init for " << mk_pp(r->get_head(), ctx.m) << std::endl;
        svector<expr*>& buffer = ctx.m_buffer;
        buffer.resize(m_num_cols);
        unsigned i = 0;
        bool new_facts = false;
        while (i < m_num_cols) {
            const unsigned idx = m_indices[i];
            expr* arg = r->get_head()->get_arg(idx);
            if (is_var(arg)) {
                const unsigned arg_idx = to_var(arg)->get_idx();
                bool is_determined = false;
                for (unsigned j = r->get_uninterpreted_tail_size(); j < r->get_tail_size(); ++j) {
                    app *elem = r->get_tail(j);
                    if (ctx.m.is_eq(elem)) {
                        expr *lhs = elem->get_arg(0);
                        expr *rhs = elem->get_arg(1);
                        if (lhs == arg) {
                            if (ctx.m.is_value(rhs)) {
                                buffer[i++] = rhs;
                                is_determined = true;
                                break;
                            }
                        } else if (rhs == arg) {
                            if (ctx.m.is_value(lhs)) {
                                buffer[i++] = lhs;
                                is_determined = true;
                                break;
                            }
                        }
                    }
                }
                if (!is_determined) {
                    delete_column(i);
                    remove_duplicates();
                    new_facts = true;
                }
            } else {
                buffer[i++] = arg;
            }
        }
        new_facts |= insert_fact(ctx, buffer, 0);
        if (new_facts)
            prune(ctx);
        return new_facts;
    }

    unsigned tuple_set::count_unique_values(ctx_t& ctx, unsigned col) const {
        bit_vector& seen = ctx.m_seen;
        seen.reset();
        seen.resize(m_num_rows);
        unsigned count = 0;
        for (unsigned i = 0; i < m_num_rows; ++i) {
            if (!seen.get(i)) {
                expr *cur = m_tuples[i*m_num_cols + col];
                ++count;
                for (unsigned j = i + 1; j < m_num_rows; ++j) {
                    if (!seen.get(j)) {
                        expr *oth = m_tuples[j*m_num_cols + col];
                        if (cur == oth) {
                            seen.set(j);
                        }
                    }
                }
            }
        }
        return count;
    }

    void tuple_set::prune(ctx_t& ctx) {
        if (m_num_cols == 0)
            return;
        while (m_num_rows > ctx.m_cutoff) {
            unsigned max_col;
            unsigned max_val = 0;
            for (unsigned i = 0; i < m_num_cols; ++i) {
                unsigned count = count_unique_values(ctx, i);
                if (count > max_val) {
                    max_col = i;
                    max_val = count;
                }
            }
            delete_column(max_col);
            remove_duplicates();
        }
    }

    void tuple_set::init_down(ctx_t& m, const rule_set& rules, fact_setter<tuple_set>& setter) {
        const func_decl_set& outputs = rules.get_output_predicates();
        for (func_decl_set::iterator I = outputs.begin(),
            E = outputs.end(); I != E; ++I) {
            func_decl* output = *I;
            const rule_vector& output_rules = rules.get_predicate_rules(output);
            for (rule_vector::const_iterator I2 = output_rules.begin(),
                E2 = output_rules.end(); I2 != E2; ++I2) {
                rule* output_rule = *I2;
                tuple_set& head_fact = setter.get(output_rule->get_decl());
                head_fact.m_num_cols = 0;
                head_fact.m_indices.reset();
                head_fact.has_tuples = true;
                setter.set_changed(output_rule->get_decl());
                m.m_buffer.reset();
                distribute_query_fact(m, m.m_buffer, 0, output_rule, setter);
            }
        }
    }

    void tuple_set::distribute_query_facts(ctx_t& ctx, const rule* r, fact_setter<tuple_set>& setter) const {
        const unsigned nrows = num_rows();
        const unsigned ncols = num_cols();
        app *head = r->get_head();
        unsigned max_vidx = 0;
        svector<expr*>& buffer = ctx.m_buffer;
        for (unsigned i = 0; i < ncols; ++i) {
            expr* arg = head->get_arg(m_indices[i]);
            if (is_var(arg)) {
                const unsigned vidx = to_var(arg)->get_idx();
                if (max_vidx < vidx) {
                    max_vidx = vidx;
                }
            }
        }
        for (unsigned i = r->get_uninterpreted_tail_size(); i < r->get_tail_size(); ++i) {
            app *elem = r->get_tail(i);
            for (unsigned j = 0; j < elem->get_num_args(); ++j) {
                expr *arg = elem->get_arg(j);
                if (is_var(arg)) {
                    const unsigned vidx = to_var(arg)->get_idx();
                    if (max_vidx < vidx) {
                        max_vidx = vidx;
                    }
                }
            }
        }
        if (nrows == 0 && ncols == 0) {
            buffer.reset();
            buffer.resize(max_vidx + 1);
            distribute_query_fact(ctx, buffer, max_vidx + 1, r, setter);
        } else {
            for (unsigned i = 0; i < nrows; ++i) {
                // Generate mapping
                buffer.reset();
                buffer.resize(max_vidx + 1);
                bool feasible = true;
                for (unsigned j = 0; j < ncols; ++j) {
                    expr *arg = head->get_arg(m_indices[j]);
                    if (is_var(arg)) {
                        const unsigned vidx = to_var(arg)->get_idx();
                        expr *cur_binding = buffer[vidx];
                        expr *new_binding = m_tuples[i*ncols + j];
                        if (cur_binding == 0) {
                            buffer[vidx] = new_binding;
                        } else {
                            if (cur_binding != new_binding) {
                                feasible = false;
                                break;
                            }
                        }
                    } else {
                        if (m_tuples[i*ncols + j] != arg) {
                            feasible = false;
                            break;
                        }
                    }
                }
                if (feasible) {
                    for (unsigned i = r->get_uninterpreted_tail_size(); i < r->get_tail_size(); ++i) {
                        app *elem = r->get_tail(i);
                        if (ctx.m.is_eq(elem)) {
                            expr *lhs = elem->get_arg(0);
                            expr *rhs = elem->get_arg(1);
                            if (is_var(lhs)) {
                                const unsigned lidx = to_var(lhs)->get_idx();
                                if (is_var(rhs)) {
                                    const unsigned ridx = to_var(rhs)->get_idx();
                                    if (buffer[lidx]) {
                                        if (buffer[ridx]) {
                                            if (buffer[lidx] != buffer[ridx]) {
                                                feasible = false;
                                            }
                                        } else {
                                            buffer[ridx] = buffer[lidx];
                                        }
                                    } else {
                                        if (buffer[ridx]) {
                                            buffer[lidx] = buffer[ridx];
                                        }
                                    }
                                } else if (ctx.m.is_value(rhs)) {
                                    if (buffer[lidx]) {
                                        if (buffer[lidx] != rhs) {
                                            feasible = false;
                                        }
                                    } else {
                                        buffer[lidx] = rhs;
                                    }
                                }
                            } else if(ctx.m.is_value(lhs)) {
                                if (is_var(rhs)) {
                                    const unsigned ridx = to_var(rhs)->get_idx();
                                    if (buffer[ridx]) {
                                        if (buffer[ridx] != lhs) {
                                            feasible = false;
                                        }
                                    } else {
                                        buffer[ridx] = lhs;
                                    }
                                } else if (ctx.m.is_value(rhs)) {
                                    if (lhs != rhs) {
                                        feasible = false;
                                    }
                                }
                            }
                        }
                    }
                }
                if (feasible) {
                    distribute_query_fact(ctx, buffer, max_vidx + 1, r, setter);
                }
            }
        }
    }

    void tuple_set::distribute_query_fact(ctx_t& ctx, svector<expr*>& buffer, unsigned offs, const rule* r, fact_setter<tuple_set>& setter) {
        bit_vector& bound_vars = ctx.m_seen;
        bound_vars.reset();
        for (unsigned i = 0; i < r->get_tail_size(); ++i) {
            app *el = r->get_tail(i);
            tuple_set& tail_fact = setter.get(el->get_decl());
            unsigned ncols = tail_fact.num_cols();
            buffer.resize(offs + ncols);
            bool new_fact = false;
            unsigned j = 0;
            while (j < ncols) {
                const unsigned arg_idx = tail_fact.m_indices[j];
                expr *arg = el->get_arg(arg_idx);
                if (is_var(arg)) {
                    const unsigned vidx = to_var(arg)->get_idx();
                    expr *var_binding = vidx < offs ? buffer[vidx] : 0;
                    if (var_binding == 0) {
                        // Variable is unbound, delete column
                        tail_fact.delete_column(j);
                        --ncols;
                        new_fact = true;
                    } else {
                        buffer[offs + j] = var_binding;
                        ++j;
                        if (!r->is_neg_tail(i)) {
                            if (bound_vars.size() <= vidx) {
                                bound_vars.resize(vidx + 1);
                            }
                            bound_vars.set(vidx);
                        }
                    }
                } else {
                    buffer[offs + j] = arg;
                    ++j;
                }
            }
            if (tail_fact.insert_fact(ctx, buffer, offs)) {
                tail_fact.prune(ctx);
                new_fact = true;
            }
            if (new_fact) {
                setter.set_changed(el->get_decl());
            }
        }
    }

    void tuple_set::intersect(ctx_t& ctx, const tuple_set& oth) {
        if (oth.m_num_cols == 0) {
            return;
        }
        if (m_num_cols == 0) {
            m_indices = oth.m_indices;
            m_tuples = oth.m_tuples;
            m_num_cols = oth.m_num_cols;
            m_num_rows = oth.m_num_rows;
            return;
        }
        unsigned_vector& old_indices = ctx.m_iter;
        svector<expr*>& old_tuples = ctx.m_buffer;
        // Make a copy of the current data
        old_indices = m_indices;
        old_tuples = m_tuples;
        const unsigned old_nrows = m_num_rows;
        const unsigned old_ncols = m_num_cols;
        // Merge the columns
        m_indices.reset();
        unsigned lidx = 0;
        unsigned ridx = 0;
        while (true) {
            if (lidx >= old_indices.size()) {
                while (ridx < oth.m_indices.size()) {
                    m_indices.push_back(oth.m_indices[ridx++]);
                }
                break;
            }
            if (ridx >= oth.m_indices.size()) {
                while (lidx < old_indices.size()) {
                    m_indices.push_back(old_indices[lidx++]);
                }
                break;
            }
            if (old_indices[lidx] < oth.m_indices[ridx]) {
                m_indices.push_back(old_indices[lidx++]);
            } else if (old_indices[lidx] > oth.m_indices[ridx]) {
                m_indices.push_back(oth.m_indices[ridx++]);
            } else {
                m_indices.push_back(old_indices[lidx++]);
                ++ridx;
            }
        }
        m_num_cols = m_indices.size();
        // Merge the tuples
        m_tuples.reset();
        m_num_rows = 0;
        for (unsigned i = 0; i < old_nrows; ++i) {
            for (unsigned j = 0; j < oth.m_num_rows; ++j) {
                m_tuples.resize((m_num_rows + 1)*m_num_cols);
                // Write the left hand fact
                for (unsigned col = 0; col < old_ncols; ++col) {
                    expr *val = old_tuples[i*old_ncols + col];
                    // Find the new column
                    unsigned new_col;
                    for (new_col = col; m_indices[new_col] != old_indices[col]; ++new_col);
                    m_tuples[m_num_rows*m_num_cols + new_col] = val;
                }
                // Write the right hand fact and check for feasability
                bool feasible = true;
                for (unsigned col = 0; col < oth.m_num_cols; ++col) {
                    expr *val = oth.m_tuples[j*oth.m_num_cols + col];
                    // Find the new column
                    unsigned new_col;
                    for (new_col = col; m_indices[new_col] != oth.m_indices[col]; ++new_col);
                    if (m_tuples[m_num_rows*m_num_cols + new_col] == 0) {
                        m_tuples[m_num_rows*m_num_cols + new_col] = val;
                    } else if (m_tuples[m_num_rows*m_num_cols + new_col] != val) {
                        feasible = false;
                        break;
                    }
                }
                if (feasible) {
                    ++m_num_rows;
                }
            }
        }
        m_tuples.resize(m_num_rows*m_num_cols);
    }

    void tuple_set::dump(ctx_t& ctx, std::ostream& outp) const {
        const unsigned ncols = num_cols();
        const unsigned nrows = num_rows();
        if (m_indices.empty())
            return;
        for (unsigned i = 0; i < nrows; ++i) {
            unsigned ipos = 0;
            for (unsigned j = 0;; ++j) {
                if (m_indices[ipos] == j) {
                    outp << " " << mk_pp(m_tuples[i*ncols + ipos], ctx.m);
                    if (++ipos == m_indices.size())
                        break;
                } else {
                    outp << " *";
                }
            }
            outp << std::endl;
        }
    }

    bool tuple_set::is_full(ctx_t& ctx, unsigned col) const {
        sort* const* domain = m_symbol->get_domain();
        const unsigned arg = m_indices[col];
        sort* srt = domain[arg];
        const sort_size& sz = srt->get_num_elements();
        if (sz.is_infinite())
            return false;
        const unsigned count = count_unique_values(ctx, col);
        if (count < sz.size())
            return false;
        else
            return true;
    }
}
