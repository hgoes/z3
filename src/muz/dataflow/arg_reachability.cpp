/*++
Copyright (c) 2015 Microsoft Corporation

Module Name:

    arg_reachability.cpp

Abstract:

    Abstract domain for tracking argument reachability.

Author:
    Henning Guenther (t-hennig)

--*/

#include "arg_reachability.h"

namespace datalog {

    const arg_reachability_info arg_reachability_info::null_fact = arg_reachability_info();

    void arg_reachability_info::init_down(ctx_t& ctx, const rule_set& rules, fact_setter<arg_reachability_info>& setter) {
        for (obj_map<func_decl, rule_vector*>::iterator I = rules.begin_grouped_rules(),
            E = rules.end_grouped_rules(); I != E; ++I) {
            func_decl *sym = I->m_key;
            rule_vector *p_rules = I->m_value;
            if (rules.is_output_predicate(sym)) {
                arg_reachability_info& fact = setter.get(sym);
                for (unsigned i = 0; i < sym->get_arity(); ++i) {
                    fact.m_reachable.set(i);
                }
                setter.set_changed(sym);
            }
            expr_free_vars& reachable_vars = ctx.m_fv;
            uint_set& seen = ctx.m_seen;
            for (rule_vector::iterator RI = p_rules->begin(),
                RE = p_rules->end(); RI != RE; ++RI) {

                const rule *rule = *RI;
                reachable_vars.reset();
                // All interpreted tail variables are reachable
                for (unsigned i = rule->get_uninterpreted_tail_size(); i < rule->get_tail_size(); ++i) {
                    reachable_vars.accumulate(rule->get_tail(i));
                }
                // All variables that occur multiple times in the uninterpreted tail are reachable,
                // because they introduce implicit equalities.
                seen.reset();
                for (unsigned i = 0; i < rule->get_uninterpreted_tail_size(); ++i) {
                    app *elem = rule->get_tail(i);
                    for (unsigned j = 0; j < elem->get_num_args(); ++j) {
                        expr *arg = elem->get_arg(j);
                        if (is_var(arg)) {
                            const arg_reachability_info& prev_fact = ctx.m_prev->get_fact(elem->get_decl());
                            // If the variable is found to be unconstrained, we can ignore it.
                            if (prev_fact.is_reachable(j)) {
                                unsigned idx = to_var(arg)->get_idx();
                                if (seen.contains(idx)) {
                                    reachable_vars.accumulate(arg);
                                } else {
                                    seen.insert(idx);
                                }
                            }
                        }
                    }
                }
                // Apply reachability info
                for (unsigned i = 0; i < rule->get_uninterpreted_tail_size(); ++i) {
                    app* elem = rule->get_tail(i);
                    bool change = false;
                    arg_reachability_info& fact = setter.get(elem->get_decl());
                    for (unsigned j = 0; j < elem->get_num_args(); ++j) {
                        expr* arg = elem->get_arg(j);
                        if (is_var(arg)) {
                            if (reachable_vars.contains(to_var(arg)->get_idx())) {
                                fact.m_reachable.set(j);
                                change = true;
                            }
                        } else {
                            fact.m_reachable.set(j);
                            change = true;
                        }
                    }
                    if (change) {
                        setter.set_changed(elem->get_decl());
                    }
                }
            }
        }
    }

    bool arg_reachability_info::init_up(arg_reachability_ctx& ctx, const rule *r) {
        expr_free_vars& reachable_vars = ctx.m_fv;
        reachable_vars.reset();
        // Put every variable that occurs in the (interpreted) tail into the reachable set
        for (unsigned i = r->get_uninterpreted_tail_size(); i < r->get_tail_size(); ++i) {
            app *interp = r->get_tail(i);
            reachable_vars.accumulate(interp);
        }
        // If a variable occurs multiple times in the head, it introduces an implicit equality constraint
        uint_set& seen = ctx.m_seen;
        seen.reset();
        for (unsigned i = 0; i < r->get_head()->get_num_args(); ++i) {
            expr *head_arg = r->get_head()->get_arg(i);
            if (is_var(head_arg)) {
                if (seen.contains(to_var(head_arg)->get_idx())) {
                    reachable_vars.accumulate(head_arg);
                } else {
                    seen.insert(to_var(head_arg)->get_idx());
                }
            }
        }
        const unsigned size = r->get_head()->get_num_args();
        bool new_info = false;
        for (unsigned i = 0; i < size; ++i) {
            if (!m_reachable.get(i)) {
                expr *head_arg = r->get_head()->get_arg(i);
                if (is_var(head_arg)) {
                    if (reachable_vars.contains(to_var(head_arg)->get_idx())) {
                        m_reachable.set(i);
                        new_info = true;
                    }
                } else {
                    m_reachable.set(i);
                    new_info = true;
                }
            }
        }
        return new_info;
    }

    bool arg_reachability_info::propagate_up(arg_reachability_ctx& ctx, const rule *r, const fact_reader<arg_reachability_info>& tail_facts) {
        expr_free_vars& reachable_vars = ctx.m_fv;
        reachable_vars.reset();
        const unsigned size = r->get_head()->get_num_args();
        // Calculate the affected variables
        for (unsigned i = 0; i < r->get_uninterpreted_tail_size(); ++i) {
            app *tail_el = r->get_tail(i);
            const arg_reachability_info& info = tail_facts.get(i);
            for (unsigned j = 0; j < tail_el->get_num_args(); ++j) {
                if (info.is_reachable(j)) {
                    expr* tail_arg = tail_el->get_arg(j);
                    reachable_vars.accumulate(tail_arg);
                }
            }
        }
        bool new_info = false;
        for (unsigned i = 0; i < size; ++i) {
            if (!m_reachable.get(i)) {
                expr* head_arg = r->get_head()->get_arg(i);
                if (is_var(head_arg)) {
                    if (reachable_vars.contains(to_var(head_arg)->get_idx())) {
                        m_reachable.set(i);
                        new_info = true;
                    }
                } else {
                    m_reachable.set(i);
                    new_info = true;
                }
            }
        }
        return new_info;
    }

    void arg_reachability_info::propagate_down(arg_reachability_ctx& ctx, const rule* r, fact_writer<arg_reachability_info>& tail_facts) const {
        taint_tracer& tr = ctx.m_tracer;
        tr.reset();
        if (!m_reachable.empty()) {
            for (unsigned i = 0; i < r->get_head()->get_num_args(); ++i) {
                expr* head_arg = r->get_head()->get_arg(i);
                if (is_var(head_arg)) {
                    if (m_reachable.get(i)) {
                        tr.set_reachable(to_var(head_arg)->get_idx());
                    }
                }
            }
        }
        for (unsigned i = r->get_uninterpreted_tail_size(); i < r->get_tail_size(); ++i) {
            tr.process(r->get_tail(i));
        }
        // Propagate reachability information
        for (unsigned i = 0; i < r->get_uninterpreted_tail_size(); ++i) {
            app *tail_elem = r->get_tail(i);
            const unsigned elem_size = tail_elem->get_num_args();
            arg_reachability_info& tail_fact = tail_facts.get(i);
            bool changed = false;
            for (unsigned j = 0; j < elem_size; ++j) {
                if (!tail_fact.m_reachable.get(j)) {
                    expr* tail_arg = tail_elem->get_arg(j);
                    if (is_var(tail_arg)) {
                        if (tr.is_reachable(to_var(tail_arg)->get_idx())) {
                            tail_fact.m_reachable.set(j);
                            changed = true;
                        }
                    } else {
                        tail_fact.m_reachable.set(j);
                        changed = true;
                    }
                }
            }
            if (changed) {
                tail_facts.set_changed(i);
            }
        }
    }

    void arg_reachability_info::join(arg_reachability_ctx& ctx, const arg_reachability_info& oth) {
         if (!oth.m_reachable.empty())
             m_reachable |= oth.m_reachable;
    }

    void arg_reachability_info::intersect(arg_reachability_ctx& ctx, const arg_reachability_info& oth) {
        if (!oth.m_reachable.empty()) {
            m_reachable &= oth.m_reachable;
        } else {
            m_reachable.fill0();
        }
    }

    void arg_reachability_info::dump(arg_reachability_ctx& ctx, std::ostream& outp) const {
        outp << "[";
        for (unsigned i = 0; i < m_reachable.size(); ++i) {
            if (m_reachable.get(i)) outp << "+";
            else outp << "-";
        }
        outp << "]";
    }

}
