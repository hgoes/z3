#include "dl_mk_rule_exploder2.h"
#include "hashtable.h"

namespace datalog {

    mk_rule_exploder2::mk_rule_exploder2(context & ctx, unsigned threshold, unsigned priority)
        : plugin(priority), m_ctx(ctx), m_new_tail(ctx.get_manager()),
        m_new_args(ctx.get_manager()), m_subst(ctx.get_manager()),
        m_simpl(ctx.get_manager()), m_threshold(threshold), m_contains_bound_var(m_bound_vars), m_cur_key(0) {
    }

    rule_set * mk_rule_exploder2::operator()(rule_set const & source) {
        tuple_set_ctx ctx(source.get_manager(), m_threshold);
        dataflow_engine<tuple_set> engine(ctx, source);
        engine.run_bottom_up();
        dataflow_engine<tuple_set> engine_down(ctx, source);
        engine_down.run_top_down();
        engine.intersect(engine_down);
        mapping_map mapping;
        rule_set* trg = alloc(rule_set, m_ctx);
        generate_mapping(engine, mapping, source, *trg);
        for (rule_set::iterator I = source.begin(),
            E = source.end(); I != E; ++I) {
            translate_rule(engine, mapping, *I, *trg);
        }
        return trg;
    }

    void mk_rule_exploder2::generate_mapping(const dataflow_engine<tuple_set>& engine, mapping_map& mappings, const rule_set& src, rule_set& trg) {
        for (dataflow_engine<tuple_set>::iterator I = engine.begin(),
            E = engine.end(); I != E; ++I) {
            func_decl* sym = I->m_key;
            const tuple_set& fact = I->m_value;
            if (fact.num_cols() > 0) {
                const unsigned narity = sym->get_arity() - fact.num_cols();
                vector<sort*> domain;
                unsigned col = 0;
                for (unsigned i = 0; i < sym->get_arity(); ++i) {
                    if (col < fact.num_cols() && i == fact.get_columns()[col]) {
                        ++col;
                    } else {
                        domain.push_back(sym->get_domain(i));
                    }
                }
                SASSERT(col == fact.num_cols());
                vector<func_decl*>& vec = mappings.insert_if_not_there2(sym, vector<func_decl*>())->get_data().m_value;
                for (unsigned i = 0; i < fact.num_rows(); ++i) {
                    func_decl *nsym = m_ctx.mk_fresh_head_predicate(sym->get_name(), symbol::null, narity, domain.c_ptr(), sym);
                    vec.push_back(nsym);
                    trg.inherit_predicate(src, sym, nsym);
                }
            } else {
                trg.inherit_predicate(src, sym, sym);
            }
        }
    }

    void mk_rule_exploder2::translate_rule(const dataflow_engine<tuple_set>& engine, const mapping_map& mappings, rule* r, rule_set& trg) {
        const unsigned psz = r->get_positive_tail_size();
        const unsigned nsz = r->get_uninterpreted_tail_size();
        m_iters.resize(psz + 1);
        m_tail_facts.resize(psz + 1);
        m_tail_syms.resize(psz + 1);
        m_bound_vars.reset();
        bool no_replacement = true;
        for (unsigned i = 0; i <= psz; ++i) {
            app *elem = i == 0 ? r->get_head() : r->get_tail(i - 1);
            func_decl *sym = elem->get_decl();
            m_iters[i] = 0;
            const tuple_set& fact = engine.get_fact(sym);
            m_tail_facts[i] = &fact;
            mapping_map::entry* entr = mappings.find_core(sym);
            if (entr) {
                m_tail_syms[i] = &entr->get_data().m_value;
                no_replacement = false;
                for (unsigned col = 0; col < fact.num_cols(); ++col)  {
                    const unsigned idx = fact.get_columns()[col];
                    expr *arg = elem->get_arg(idx);
                    if (is_var(arg)) {
                        m_bound_vars.insert(to_var(arg)->get_idx());
                    }
                }
            } else {
                m_tail_syms[i] = 0;
            }
        }
        if (no_replacement) {
            trg.add_rule(r);
        } else {
            app_ref common_tail(m_ctx.get_manager());
            m_exluded_tails.reset();
            rule* common_tail_rule;
            if (m_threshold > 1) {
                common_tail_rule = create_common_tail(r, common_tail);
            } else {
                common_tail_rule = 0;
            }
            bool valid_iter = true;
            while (valid_iter) {
                // Generate variable bindings
                bool feasible = true;
                m_var_bindings.reset();
                for (unsigned i = 0; i <= psz; ++i) {
                    const vector<func_decl*>* repl = m_tail_syms[i];
                    if (repl != 0) {
                        const tuple_set* fact = m_tail_facts[i];
                        const unsigned num = m_iters[i];
                        app* elem = i == 0 ? r->get_head() : r->get_tail(i - 1);
                        if (fact->num_rows() == 0 && fact->num_cols() != 0) {
                            feasible = false;
                            break;
                        }
                        for (unsigned j = 0; j < fact->num_cols(); ++j) {
                            const unsigned arg_idx = fact->get_columns()[j];
                            expr* arg = elem->get_arg(arg_idx);
                            expr* inst = fact->get_tuples()[num*fact->num_cols() + j];
                            if (is_var(arg)) {
                                const unsigned vidx = to_var(arg)->get_idx();
                                if (m_var_bindings.size() <= vidx) {
                                    m_var_bindings.resize(vidx + 1);
                                    m_var_bindings[vidx] = inst;
                                } else if (m_var_bindings[vidx] == 0) {
                                    m_var_bindings[vidx] = inst;
                                } else if (m_var_bindings[vidx] != inst) {
                                    feasible = false;
                                    break;
                                }
                            } else if (arg != inst) {
                                feasible = false;
                                break;
                            }
                        }
                        if (!feasible) {
                            break;
                        }
                    }
                }
                if (feasible) {
                    // Create the new rule
                    m_new_tail.reset();
                    m_new_tail_neg.reset();
                    m_subst.set_bindings(m_var_bindings.size(), m_var_bindings.c_ptr());
                    expr_ref result(m_ctx.get_manager());
                    proof_ref pr(m_ctx.get_manager());
                    app *new_head;
                    if (common_tail.get()) {
                        m_new_tail.push_back(common_tail.get());
                        m_new_tail_neg.push_back(false);
                    }
                    // Transform the positive tail
                    for (unsigned i = 0; i <= psz; ++i) {
                        if (i != 0 && m_exluded_tails.contains(i - 1))
                            continue;
                        const unsigned num = m_iters[i];
                        const tuple_set* fact = m_tail_facts[i];
                        const vector<func_decl*>* repl = m_tail_syms[i];
                        app* elem = i == 0 ? r->get_head() : r->get_tail(i - 1);
                        m_new_args.reset();
                        bool mk_new = false;
                        unsigned col = 0;
                        for (unsigned j = 0; j < elem->get_num_args(); ++j) {
                            if (col < fact->num_cols() && j == fact->get_columns()[col]) {
                                col++;
                                continue;
                            }
                            expr* arg = elem->get_arg(j);
                            result = 0;
                            m_subst(arg, result);
                            if (result.get() != 0) {
                                m_new_args.push_back(result.get());
                                mk_new = true;
                            } else {
                                m_new_args.push_back(arg);
                            }
                        }
                        app* nelem;
                        if (repl) {
                            nelem = m_ctx.get_manager().mk_app((*repl)[num], m_new_args.size(), m_new_args.c_ptr());
                        } else if (mk_new) {
                            nelem = m_ctx.get_manager().mk_app(elem->get_decl(), m_new_args.size(), m_new_args.c_ptr());
                        } else {
                            nelem = elem;
                        }
                        if (i == 0) {
                            new_head = nelem;
                        } else {
                            m_new_tail.push_back(nelem);
                            m_new_tail_neg.push_back(false);
                        }
                    }
                    // Transform the negative tail
                    for (unsigned i = psz; i < nsz; ++i) {
                        if (m_exluded_tails.contains(i))
                            continue;
                        app* elem = r->get_tail(i);
                        m_new_args.reset();
                        bool mk_new = false;
                        for (unsigned j = 0; j < elem->get_num_args(); ++j) {
                            expr* arg = elem->get_arg(j);
                            result = 0;
                            m_subst(arg, result);
                            if (result.get() != 0) {
                                m_new_args.push_back(result.get());
                                mk_new = true;
                            } else {
                                m_new_args.push_back(arg);
                            }
                        }
                        app* repl = get_negation_replacement(elem->get_decl(), m_new_args, engine, mappings, trg);
                        if (repl != 0) {
                            m_new_tail.push_back(repl);
                            m_new_tail_neg.push_back(true);
                        }
                    }
                    // Transform the interpreted tail
                    proof_ref proof(m_ctx.get_manager());
                    for (unsigned i = r->get_uninterpreted_tail_size(); i < r->get_tail_size(); ++i) {
                        if (m_exluded_tails.contains(i))
                            continue;
                        app *elem = r->get_tail(i);
                        m_subst(elem, result);
                        m_ctx.get_rewriter()(result);
                        if (m_ctx.get_manager().is_false(result)) {
                            //std::cout << "Simplified " << mk_pp(elem, m_ctx.get_manager()) << " to false." << std::endl;
                            if (!r->is_neg_tail(i)) {
                                feasible = false;
                                break;
                            }
                        } else if (m_ctx.get_manager().is_true(result)) {
                            //std::cout << "Simplified " << mk_pp(elem, m_ctx.get_manager()) << " to true." << std::endl;
                            if (r->is_neg_tail(i)) {
                                feasible = false;
                                break;
                            }
                        } else {
                            SASSERT(is_app(result));
                            /*if (nelem != elem) {
                                std::cout << "Simplified " << mk_pp(elem, m_ctx.get_manager()) << " to " << mk_pp(nelem, m_ctx.get_manager()) << "." << std::endl;
                            }*/
                            m_new_tail.push_back(to_app(result));
                            m_new_tail_neg.push_back(r->is_neg_tail(i));
                        }
                    }
                    if (feasible) {
                        if (common_tail_rule) {
                            trg.add_rule(common_tail_rule);
                            // Only add once
                            common_tail_rule = 0;
                        }
                        rule* nrule = m_ctx.get_rule_manager().mk(new_head, m_new_tail.size(), m_new_tail.c_ptr(), m_new_tail_neg.c_ptr());
                        trg.add_rule(nrule);
                    }
                }
                valid_iter = false;
                for (unsigned i = 0; i <= psz; ++i) {
                    if (++m_iters[i] >= m_tail_facts[i]->num_rows()) {
                        m_iters[i] = 0;
                    } else {
                        valid_iter = true;
                        break;
                    }
                }
            }
        }
    }

    app* mk_rule_exploder2::get_negation_replacement(func_decl* sym, expr_ref_vector& inst, const dataflow_engine<tuple_set>& engine, const mapping_map& mappings, rule_set& trg) {
        const tuple_set& fact = engine.get_fact(sym);
        if (fact.num_cols() == 0) {
            return m_ctx.get_manager().mk_app(sym, inst.size(), inst.c_ptr());
        }
        // Are all parameters determined?
        bool all_determined = true;
        for (unsigned col = 0; col < fact.num_cols(); ++col) {
            if (is_var(inst.get(fact.get_columns()[col]))) {
                all_determined = false;
                break;
            }
        }
        if (all_determined) {
            // Find the matching row
            for (unsigned row = 0; row < fact.num_rows(); ++row) {
                bool matches = true;
                for (unsigned col = 0; col < fact.num_cols(); ++col) {
                    if (fact.get_tuples()[row*fact.num_cols() + col] != inst.get(fact.get_columns()[col])) {
                        matches = false;
                        break;
                    }
                }
                if (matches) {
                    const vector<func_decl*>& repls = mappings.find(sym);
                    // Fix the arguments
                    for (unsigned col = 0; col < fact.num_cols(); ++col) {
                        inst.erase(fact.get_columns()[col] - col);
                    }
                    return m_ctx.get_manager().mk_app(repls[row], inst.size(), inst.c_ptr());
                }
            }
            // No row matches, the predicate is false
            return 0;
        }
        if (m_cur_key == 0) {
            m_cur_key = alloc(negation_repl_key, m_ctx.get_manager());
        }
        m_cur_key->m_symbol = sym;
        m_cur_key->m_inst.resize(fact.num_cols());
        for (unsigned i = 0; i < fact.num_cols(); ++i) {
            expr* arg = inst.get(fact.get_columns()[i]);
            if (is_var(arg)) {
                m_cur_key->m_inst[i] = 0;
            } else {
                m_cur_key->m_inst[i] = arg;
            }
        }
        m_cur_key->m_hash_cache = 0;
        obj_map<negation_repl_key, func_decl*>::obj_map_entry* entry = m_negation_repl.insert_if_not_there2(m_cur_key, 0);
        func_decl* &result = entry->get_data().m_value;
        if (result == 0) {
            const vector<func_decl*>& repls = mappings.find(sym);
            vector<sort*> domain;
            vector<sort*> var_domain;
            unsigned col = 0;
            for (unsigned i = 0; i < sym->get_arity(); ++i) {
                if (col < fact.num_cols() && fact.get_columns()[col] == i) {
                    if (is_var(inst.get(i))) {
                        domain.push_back(sym->get_domain(i));
                    }
                    ++col;
                } else {
                    domain.push_back(sym->get_domain(i));
                    var_domain.push_back(sym->get_domain(i));
                }
            }
            // Create the replacement symbol
            result = m_ctx.mk_fresh_head_predicate(sym->get_name(), symbol("neg"), domain.size(), domain.c_ptr(), sym);
            vector<expr*> vars;
            vars.resize(var_domain.size());
            // Create the free variables
            for (unsigned i = 0; i < var_domain.size(); ++i) {
                vars[i] = m_ctx.get_manager().mk_var(i, var_domain[i]);
            }
            // Create the rules
            vector<expr*> head_args;
            vector<expr*> body_args;
            for (unsigned i = 0; i < fact.num_rows(); ++i) {
                // Check if the fact is compatible with the instantiation
                unsigned col = 0;
                unsigned vidx = 0;
                bool compatible = true;
                for (unsigned j = 0; j < sym->get_arity(); ++j) {
                    if (col < fact.num_cols() && fact.get_columns()[col] == j) {
                        if (is_var(inst.get(j))) {
                            head_args.push_back(fact.get_tuples()[i*fact.num_cols() + col]);
                        } else if (inst.get(j) != fact.get_tuples()[i*fact.num_cols() + col]) {
                            compatible = false;
                            break;
                        }
                        ++col;
                    } else {
                        head_args.push_back(vars[vidx]);
                        body_args.push_back(vars[vidx]);
                        ++vidx;
                    }
                }
                if (compatible) {
                    app* head = m_ctx.get_manager().mk_app(result, head_args.size(), head_args.c_ptr());
                    app* body = m_ctx.get_manager().mk_app(repls[i], body_args.size(), body_args.c_ptr());
                    rule* nrule = m_ctx.get_rule_manager().mk(head, 1, &body);
                    trg.add_rule(nrule);
                }
                head_args.reset();
                body_args.reset();
            }
            m_cur_key = 0;
        }
        // Fit the arguments
        unsigned offset = 0;
        for (unsigned col = 0; col < fact.num_cols(); ++col) {
            const unsigned idx = fact.get_columns()[col];
            if (!is_var(inst.get(idx - offset))) {
                inst.erase(idx - offset);
                ++offset;
            }
        }
        return m_ctx.get_manager().mk_app(result, inst.size(), inst.c_ptr());
    }
    rule* mk_rule_exploder2::create_common_tail(const rule* r, app_ref& common_tail) {
        // Construct the common part of all fragments
        m_new_tail.reset();
        m_new_tail_neg.reset();
        // Holds the variables for the predicate
        m_var_bindings.reset();
        m_var_sorts.reset();
        for (unsigned i = 0; i < r->get_tail_size(); ++i) {
            if (i < r->get_positive_tail_size() && m_tail_syms[i + 1]) {
                continue;
            }
            app *elem = r->get_tail(i);
            m_contains_bound_var.reset();
            m_contains_bound_var.process(elem);
            if (!m_contains_bound_var.m_contains_bound_var) {
                m_exluded_tails.insert(i);
                m_new_tail.push_back(elem);
                m_new_tail_neg.push_back(r->is_neg_tail(i));
                // Add variables to the arguments
                const unsigned sz = m_contains_bound_var.m_unbound_vars.size();
                for (unsigned j = 0; j < sz; ++j) {
                    var *cur_var = m_contains_bound_var.m_unbound_vars[j];
                    bool not_in = true;
                    for (unsigned k = 0; k < m_var_bindings.size(); ++k) {
                        if (m_var_bindings[k] == cur_var) {
                            not_in = false;
                            break;
                        }
                    }
                    if (not_in) {
                        m_var_bindings.push_back(cur_var);
                        m_var_sorts.push_back(m_ctx.get_manager().get_sort(cur_var));
                    }
                }
                for (unsigned j = 0; j < elem->get_num_args(); ++j) {
                    expr *arg = elem->get_arg(j);
                    if (is_var(arg)) {
                        bool not_in = true;
                        for (unsigned k = 0; k < m_var_bindings.size(); ++k) {
                            if (m_var_bindings[k] == arg) {
                                not_in = false;
                                break;
                            }
                        }
                        if (not_in) {
                            m_var_bindings.push_back(arg);
                            m_var_sorts.push_back(elem->get_decl()->get_domain(j));
                        }
                    }
                }
            }
        }
        if (!m_new_tail.empty()) {
            func_decl *common_tail_sym = m_ctx.mk_fresh_head_predicate(r->get_decl()->get_name(), symbol("common"), m_var_bindings.size(), m_var_sorts.c_ptr());
            common_tail = m_ctx.get_manager().mk_app(common_tail_sym, m_var_bindings.size(), m_var_bindings.c_ptr());
            return m_ctx.get_rule_manager().mk(common_tail, m_new_tail.size(), m_new_tail.c_ptr(), m_new_tail_neg.c_ptr());
        } else {
            return 0;
        }
    }
}
