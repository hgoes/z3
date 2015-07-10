/*++
Copyright (c) 2015 Microsoft Corporation

Module Name:

    dl_mk_coi_arg_filter.cpp

Abstract:

    Rule transformer that removes arguments of predicates if they are out of
    the cone of influence of the output predicates.

Author:
    Henning Guenther (t-hennig)

--*/

#include "dl_mk_coi_arg_filter.h"
#include "model_converter.h"
#include "map.h"
#include "model_smt2_pp.h"
#include "ast_util.h"

namespace datalog {

    class mk_coi_arg_filter::coi_arg_model_converter : public model_converter {
        ast_manager& m;
        arg_reachability::fact_db m_facts;
        repl_map m_replacements;
    public:
        coi_arg_model_converter(ast_manager& _m, const arg_reachability& eng, const repl_map& repl) : m(_m), m_facts(eng.get_facts()), m_replacements(repl) {}

        virtual void operator()(model_ref& mdl) {
            TRACE("dl", model_smt2_pp(tout, m, *mdl, 0););
            model_ref old_model = alloc(model, m);
            for (repl_map::iterator I = m_replacements.begin(),
                E = m_replacements.end(); I != E; ++I) {
                func_decl *old_p = I->m_value;
                func_decl *new_p = I->m_key;
                const arg_reachability_info& fact = m_facts.get(old_p, arg_reachability_info::null_fact);
                func_interp* old_fi = alloc(func_interp, m, old_p->get_arity());
                TRACE("dl", tout << mk_pp(old_p, m) << " " << mk_pp(new_p, m) << "\n";
                            for (unsigned j = 0; j < old_p->get_arity(); ++j) {
                                tout << (fact.is_reachable(j) ? "1" : "0");
                            }
                            tout << "\n";);
                if (new_p->get_arity() == 0) {
                    old_fi->set_else(mdl->get_const_interp(new_p));
                } else {
                    expr_ref_vector subst(m);
                    expr_ref tmp(m);
                    var_subst vs(m, false);
                    for (unsigned i = 0; i < old_p->get_arity(); ++i) {
                        if (!fact.is_reachable(i)) {
                            subst.push_back(m.mk_var(i, old_p->get_domain(i)));
                        }
                    }
                    func_interp* new_fi = mdl->get_func_interp(new_p);
                    if (!new_fi) {
                        TRACE("dl", tout << new_p->get_name() << " has no value in the current model\n";);
                        dealloc(old_fi);
                        continue;
                    }
                    if (!new_fi->is_partial()) {
                        TRACE("dl", tout << mk_pp(new_fi->get_else(), m) << "\n";);
                        vs(new_fi->get_else(), subst.size(), subst.c_ptr(), tmp);
                        old_fi->set_else(tmp);
                    }
                    unsigned num_entries = new_fi->num_entries();
                    for (unsigned j = 0; j < num_entries; ++j) {
                        expr_ref res(m);
                        expr_ref_vector args(m);
                        func_entry const* e = new_fi->get_entry(j);
                        for (unsigned k = 0, l = 0; k < old_p->get_arity(); ++k) {
                            if (!fact.is_reachable(k)) {
                                vs(e->get_arg(l++), subst.size(), subst.c_ptr(), tmp);
                                args.push_back(tmp);
                            } else {
                                args.push_back(m.mk_var(k, old_p->get_domain(k)));
                            }
                            SASSERT(l <= new_p->get_arity());
                        }
                        vs(e->get_result(), subst.size(), subst.c_ptr(), res);
                        old_fi->insert_entry(args.c_ptr(), res.get());
                    }
                    old_model->register_decl(old_p, old_fi);
                }
            }
            // register values that have not been sliced.
            unsigned sz = mdl->get_num_constants();
            for (unsigned i = 0; i < sz; ++i) {
                func_decl *c = mdl->get_constant(i);
                if (!m_replacements.contains(c)) {
                    old_model->register_decl(c, mdl->get_const_interp(c));
                }
            }
            sz = mdl ->get_num_functions();
            for (unsigned i = 0; i < sz; ++i) {
                func_decl* f = mdl->get_function(i);
                if (!m_replacements.contains(f)) {
                    func_interp *fi = mdl->get_func_interp(f);
                    old_model->register_decl(f, fi->copy());
                }
            }
            mdl = old_model;
            TRACE("dl", model_smt2_pp(tout, m, *mdl, 0););
        }

        virtual model_converter* translate(ast_translation & translator) {
            UNREACHABLE();
            return 0;
        }
    };

    rule_set * mk_coi_arg_filter::operator()(rule_set const & source) {
        arg_reachability_ctx ctx1(source.get_manager());
        arg_reachability e1(ctx1, source);
        arg_reachability_ctx ctx2(source.get_manager(),&e1);
        arg_reachability e2(ctx2, source);
        e1.run_bottom_up();
        e2.run_top_down();
        e1.intersect(e2);
        TRACE("dl", e1.dump(tout << "Argument COI:" << std::endl););
        rule_set *result = transform(m_replacements, source, e1);
        if (m_context.get_model_converter()) {
            m_context.add_model_converter(alloc(coi_arg_model_converter, m_context.get_manager(), e1, m_replacements));
        }
        return result;
    }

    rule_set* mk_coi_arg_filter::transform(repl_map& repl, rule_set const & source, arg_reachability& engine) {
        scoped_ptr<rule_set> new_rules = alloc(rule_set, m_context);
        expr_free_vars fv;
        const unsigned num_rules = source.get_num_rules();
        for (unsigned i = 0; i < num_rules; ++i) {
            rule *cur = source.get_rule(i);
            const arg_reachability_info& head_reach = engine.get_fact(cur->get_decl());
            app *new_head = get_replacement(repl, source, cur->get_head(), head_reach);
            bool changed = new_head != cur->get_head();
            app_ref_vector new_tail(m);
            svector<bool> new_tail_neg;
            for (unsigned j = 0; j < cur->get_uninterpreted_tail_size(); ++j) {
                app *cur_tail_el = cur->get_tail(j);
                const arg_reachability_info& tail_reach = engine.get_fact(cur_tail_el->get_decl());
                app *new_tail_el = get_replacement(repl, source, cur_tail_el, tail_reach);
                changed |= new_tail_el != cur_tail_el;
                new_tail.push_back(new_tail_el);
                new_tail_neg.push_back(cur->is_neg_tail(j));
            }
            if (changed) {
                rule_manager& rm = m_context.get_rule_manager();
                expr_ref_vector conjs(m);
                for (unsigned j = cur->get_uninterpreted_tail_size(); j < cur->get_tail_size(); ++j) {
                    conjs.push_back(cur->get_tail(j));
                }
                flatten_and(conjs);
                fv.accumulate(new_head);
                for (unsigned j = 0; j < new_tail.size(); ++j) {
                    fv.accumulate(new_tail[j].get());
                }

                rm.fix_unbound_vars(fv, conjs, false);
                fv.reset();

                for (unsigned j = 0; j < conjs.size(); ++j) {
                    new_tail.push_back(to_app(conjs[j].get()));
                    new_tail_neg.push_back(false);
                }

                rule* new_rule = rm.mk(new_head, new_tail.size(), new_tail.c_ptr(), new_tail_neg.c_ptr());
                if (m_context.generate_proof_trace()) {
                    rm.mk_rule_asserted_proof(*new_rule);
                }
                new_rules->add_rule(new_rule);
            } else {
                new_rules->add_rule(cur);
            }
        }
        for (rule_set::decl2rules::iterator I = source.begin_grouped_rules(),
            E = source.end_grouped_rules(); I != E; ++I) {

            func_decl *orig_pred = I->m_key;
            func_decl *repl_pred;
            if (repl.find(orig_pred, repl_pred)) {
                new_rules->inherit_predicate(source, orig_pred, repl_pred);
            } else {
                new_rules->inherit_predicate(source, orig_pred, orig_pred);
            }
        }
        new_rules->close();
        return new_rules.detach();
    }

    app* mk_coi_arg_filter::get_replacement(repl_map& mp, rule_set const & source, app *orig, const arg_reachability_info& info) {
        func_decl *repl = get_replacement(mp, source, orig->get_decl(), info);
        if (repl == 0) {
            return orig;
        } else {
            vector<expr*> new_args;
            for (unsigned i = 0; i < orig->get_num_args(); ++i) {
                if (info.is_reachable(i)) {
                    new_args.push_back(orig->get_arg(i));
                }
            }
            return m.mk_app(repl, new_args.c_ptr());
        }
    }

    func_decl* mk_coi_arg_filter::get_replacement(repl_map& mp, rule_set const & source, func_decl *orig, const arg_reachability_info& info) {
        if (info.all_reachable())
            return 0;
        repl_map::obj_map_entry* entry = mp.insert_if_not_there2(orig, 0);
        if (entry->get_data().m_value != 0) {
            return entry->get_data().m_value;
        } else {
            vector<sort*> new_domain;
            for (unsigned i = 0; i < orig->get_arity(); ++i) {
                if (info.is_reachable(i)) {
                    new_domain.push_back(orig->get_domain(i));
                }
            }
            func_decl *new_decl = m_context.mk_fresh_head_predicate(orig->get_name(), /*symbol::null*/symbol("slice"),
                new_domain.size(), new_domain.c_ptr(), orig);
            entry->get_data().m_value = new_decl;
            return new_decl;
        }
    }
}