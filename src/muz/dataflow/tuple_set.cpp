#include "tuple_set.h"

namespace datalog {

    const tuple_set tuple_set::null_fact = tuple_set();

#if 0
    void tuple_set::learn_tuples(tuple_set_ctx& ctx, app* tup, const tuple_set& var_facts) {
        // If the argument is instantiated using an unbounded variable,
        // make the argument unbounded.
        unsigned_vector to_delete;
        unsigned column;
        for (unsigned i = 0; i < m_indices.size(); ++i) {
            expr* arg = tup->get_arg(m_indices[i]);
            if (is_var(arg)) {
                if (!var_facts.is_finite(to_var(arg)->get_idx(), column)) {
                    to_delete.push_back(i);
                }
            }
        }
        if (!to_delete.empty()) {
            delete_columns(to_delete);
            remove_duplicates();
        }
        const unsigned num_cols = m_indices.size();
        unsigned num_rows = m_tuples.size() / num_cols;

        const unsigned var_num_cols = var_facts.m_indices.size();
        const unsigned var_num_rows = var_facts.m_tuples.size() / var_num_cols;
        // Begin to iterate over all facts
        for (unsigned cur_fact = 0; cur_fact < var_num_rows; ++cur_fact) {
            // Write the fact into the buffer.
            ctx.m_buffer.resize(num_cols);
            for (unsigned arg_idx = 0; arg_idx < num_cols; ++arg_idx) {
                const unsigned arg_num = m_indices[arg_idx];
                expr* arg = tup->get_arg(arg_num);
                if (is_var(arg)) {
                    unsigned var_fact_column;
                    bool is_finite = var_facts.is_finite(to_var(arg)->get_idx(), var_fact_column);
                    SASSERT(is_finite);
                    arg = var_facts.m_tuples[cur_fact*var_num_cols + var_fact_column];
                }
                ctx.m_buffer[arg_idx] = arg;
            }
            // Check if the fact is already known
            bool known = false;
            for (unsigned i = 0; i < num_rows; ++i) {
                bool same = true;
                for (unsigned j = 0; j < num_cols; ++j) {
                    if (ctx.m_buffer[j] != m_tuples[i*num_cols + j]) {
                        same = false;
                        break;
                    }
                }
                if (same) {
                    known = true;
                    break;
                }
            }
            if (!known) {
                m_tuples.resize((num_rows + 1)*num_cols);
                for (unsigned i = 0; i < num_cols; ++i) {
                    m_tuples[num_rows*num_cols + 1] = ctx.m_buffer[i];
                }
                ++num_rows;
            }
        }
    }
#endif

    bool tuple_set::insert_fact(ctx_t& ctx, svector<expr*> fact_buffer, unsigned fact_offset) {
        //const unsigned ncols = num_cols();
        //const unsigned nrows = num_rows();
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
        //unsigned_vector& sizes = ctx.m_sizes;
        svector<const tuple_set*>& tail_facts = ctx.m_tail_facts;
        svector<expr*>& buffer = ctx.m_buffer;
        const unsigned utail_size = r->get_positive_tail_size();
        //unsigned ncols = num_cols();
        //unsigned nrows = num_rows();
        //std::cout << "Deduce for " << r->get_decl()->get_name().bare_str() << "(" << m_num_cols << " cols, " << m_num_rows << " rows)" << std::endl;
        iter.resize(utail_size);
        //sizes.resize(utail_size);
        tail_facts.resize(utail_size);
        //buffer.reset();
        //bool all_empty = true;
        //unsigned sz = 1;
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
            //if (fact.m_num_rows != 0) {
            //    sz *= fact.m_num_rows;
            //}
            iter[i] = 0;
            //if (sz == 0) {
                //if (cols != 0) {
                //    return false; // We are joining with an empty table
                //}
            //} else {
            //    all_empty = false;
            //}
            //sizes[i] = sz;
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
        //std::cout << "Processing " << sz << " rows." << std::endl;
        //if (all_empty)
        //    return deduce_base_facts(ctx, r);
        bool new_facts = false;
        bool valid_iter = true;
        while(valid_iter) {
            bool feasible = true;
            buffer.fill(0);
            // XXX: Urg...
            //memset(buffer.c_ptr(), 0, buffer.size()*sizeof(expr*));
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
        //unsigned ncols = m_indices.size();
        //if (ncols == 0)
        //    return true;
        buffer.resize(m_num_cols);
        unsigned i = 0;
        bool new_facts = false;
        while (i < m_num_cols) {
            const unsigned idx = m_indices[i];
            expr* arg = r->get_head()->get_arg(idx);
            if (is_var(arg)) {
                delete_column(i);
                //--ncols;
                remove_duplicates();
                new_facts = true;
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
}
