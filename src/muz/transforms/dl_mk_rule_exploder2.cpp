#include "dl_mk_rule_exploder2.h"
#include "hashtable.h"

namespace datalog {

    mk_rule_exploder2::mk_rule_exploder2(context & ctx, unsigned threshold, unsigned priority)
        : plugin(priority), m_ctx(ctx), m_new_tail(ctx.get_manager()),
        m_new_args(ctx.get_manager()), m_subst(ctx.get_manager()),
        m_simpl(ctx.get_manager()), m_threshold(threshold) {

    }

    rule_set * mk_rule_exploder2::operator()(rule_set const & source) {
        //std::cout << "Old rules:" << std::endl;
        //source.display(std::cout);
        std::cout << std::endl << "Analysis:" << std::endl;
        tuple_set_ctx ctx(source.get_manager(), m_threshold);
        dataflow_engine<tuple_set> engine(ctx, source);
        engine.run_bottom_up();
        engine.dump(std::cout);
        //std::cout << std::endl << "New rules:" << std::endl;
        mapping_map mapping;
        rule_set* trg = alloc(rule_set, m_ctx);
        generate_mapping(engine, mapping, source, *trg);
        for (rule_set::iterator I = source.begin(),
            E = source.end(); I != E; ++I) {
            translate_rule(engine, mapping, *I, *trg);
        }
        //trg->display(std::cout);
        trg->close();
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
        const unsigned sz = r->get_uninterpreted_tail_size() + 1;
        m_iters.resize(sz);
        m_tail_facts.resize(sz);
        m_tail_syms.resize(sz);
        bool no_replacement = true;
        for (unsigned i = 0; i < sz; ++i) {
            func_decl* sym = i == 0 ? r->get_decl() : r->get_decl(i - 1);
            m_iters[i] = 0;
            m_tail_facts[i] = &engine.get_fact(sym);
            mapping_map::entry* entr = mappings.find_core(sym);
            if (entr) {
                m_tail_syms[i] = &entr->get_data().m_value;
                no_replacement = false;
            } else {
                m_tail_syms[i] = 0;
            }
        }
        if (no_replacement) {
            trg.add_rule(r);
        } else {
            bool valid_iter = true;
            while (valid_iter) {
                // Generate variable bindings
                bool feasible = true;
                m_var_bindings.reset();
                m_true.reset();
                m_true.resize(sz);
                for (unsigned i = 0; i < sz; ++i) {
                    const vector<func_decl*>* repl = m_tail_syms[i];
                    if (repl != 0) {
                        const tuple_set* fact = m_tail_facts[i];
                        const unsigned num = m_iters[i];
                        app* elem = i == 0 ? r->get_head() : r->get_tail(i - 1);
                        bool is_neg = i == 0 ? false : r->is_neg_tail(i - 1);
                        if (fact->num_rows() == 0 && fact->num_cols() != 0) {
                            if (is_neg) {
                                m_true.set(i);
                            } else {
                                feasible = false;
                                break;
                            }
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
                                    if (is_neg) {
                                        m_true.set(i);
                                    } else {
                                        feasible = false;
                                        break;
                                    }
                                }
                            } else if (arg != inst) {
                                if (is_neg) {
                                    m_true.set(i);
                                } else {
                                    feasible = false;
                                    break;
                                }
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
                    for (unsigned i = 0; i < sz; ++i) {
                        if (m_true.get(i))
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
                        }  else {
                            nelem = elem;
                        }
                        if (i == 0) {
                            new_head = nelem;
                        } else {
                            m_new_tail.push_back(nelem);
                            m_new_tail_neg.push_back(r->is_neg_tail(i - 1));
                        }
                    }
                    // Transform the interpreted tail
                    for (unsigned i = r->get_uninterpreted_tail_size(); i < r->get_tail_size(); ++i) {
                        app *elem = r->get_tail(i);
                        m_new_args.reset();
                        for (unsigned j = 0; j < elem->get_num_args(); ++j) {
                            expr* arg = elem->get_arg(j);
                            result = 0;
                            m_subst(arg, result);
                            if (result.get() == 0) {
                                m_new_args.push_back(arg);
                            } else {
                                m_new_args.push_back(result.get());
                            }
                        }
                        result = 0;
                        m_simpl.reset();
                        m_simpl.mk_app(elem->get_decl(), m_new_args.size(), m_new_args.c_ptr(), result);
                        expr *nelem = result.get();
                        if (nelem == 0) {
                            m_new_tail.push_back(elem);
                            m_new_tail_neg.push_back(r->is_neg_tail(i));
                        } else if (m_ctx.get_manager().is_false(nelem)) {
                            //std::cout << "Simplified " << mk_pp(elem, m_ctx.get_manager()) << " to false." << std::endl;
                            if (!r->is_neg_tail(i)) {
                                feasible = false;
                                break;
                            }
                        } else if (m_ctx.get_manager().is_true(nelem)) {
                            //std::cout << "Simplified " << mk_pp(elem, m_ctx.get_manager()) << " to true." << std::endl;
                            if (r->is_neg_tail(i)) {
                                feasible = false;
                                break;
                            }
                        } else {
                            SASSERT(is_app(nelem));
                            //std::cout << "Simplified " << mk_pp(elem, m_ctx.get_manager()) << " to " << mk_pp(nelem,m_ctx.get_manager()) << "." << std::endl;
                            m_new_tail.push_back(to_app(nelem));
                            m_new_tail_neg.push_back(r->is_neg_tail(i));
                        }
                    }
                    if (feasible) {
                        rule* nrule = m_ctx.get_rule_manager().mk(new_head, m_new_tail.size(), m_new_tail.c_ptr(), m_new_tail_neg.c_ptr());
                        trg.add_rule(nrule);
                    }
                }
                valid_iter = false;
                for (unsigned i = 0; i < m_iters.size(); ++i) {
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
}
