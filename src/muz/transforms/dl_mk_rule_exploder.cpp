#include "dl_mk_rule_exploder.h"
#include "stopwatch.h"

namespace datalog {
    
    mk_rule_exploder::mk_rule_exploder(context & ctx, unsigned priority)
        : plugin(priority), m_context(ctx) {

    }

    void mk_rule_exploder::set_rule(const rule* r) {
        m_rule = r;
        m_fixed.reset();
        m_tail_state.resize(r->get_uninterpreted_tail_size());
    }

    /* Find variables that are fixed in the head.
       Return false if there is a conflict.
    */
    bool mk_rule_exploder::get_fixed_head(const todo_entry& cur) {
        if (cur.m_inst.empty()) return true;
        unsigned inst_pos = 0;
        for (unsigned head_pos = 0; head_pos < m_rule->get_head()->get_num_args(); ++head_pos) {
            expr* head_arg = m_rule->get_head()->get_arg(head_pos);
            if (cur.m_fact.get(head_pos).is_finite()) {
                if (is_var(head_arg)) {
                    if (!fix_var(head_arg, cur.m_inst[inst_pos])) {
                        return false;
                    }
                } else {
                    if (head_arg != cur.m_inst[inst_pos]) {
                        return false;
                    }
                }
                inst_pos++;
            }
        }
        return true;
    }
    /* Fix a variable with a constant.
       Return false if the variable was already fixed with another constant.
    */
    bool mk_rule_exploder::fix_var(expr* var, expr* c) {
        fix_descr cur;
        if (m_fixed.find(var, cur)) {
            return cur.m_type == FIXED_CONST &&
                cur.m_const == c;
        } else {
            cur.m_type = FIXED_CONST;
            cur.m_const = c;
            m_fixed.insert(var, cur);
            return true;
        }
    }
    expr* mk_rule_exploder::fix_expr(expr* orig) {
        if (is_app(orig)) {
            return fix_app(to_app(orig));
        } else if (is_var(orig)) {
            fix_descr res;
            if (m_fixed.find(orig, res)) {
                switch (res.m_type) {
                case FIXED_CONST:
                    return res.m_const;
                case FIXED_ITER:
                    return *m_iters[res.m_iterator].m_cur;
                }
            } else {
                return 0;
            }
        } else {
            return 0;
        }
    }
    app* mk_rule_exploder::fix_app(app* orig) {
        bool keep = true;
        vector<expr*> repl;
        for (unsigned i = 0; i < orig->get_num_args(); ++i) {
            expr* narg = fix_expr(orig->get_arg(i));
            if (narg != 0) {
                if (keep) {
                    keep = false;
                    repl.resize(orig->get_num_args());
                    for (unsigned j = 0; j < i; ++j) {
                        repl[j] = orig->get_arg(j);
                    }
                }
                repl[i] = narg;
            } else if (!keep) {
                repl[i] = orig->get_arg(i);
            }
        }
        if (keep) return 0;
        else {
            // Special case: Optimize equalities
            ast_manager& m = m_context.get_manager();
            if (m.is_eq(orig->get_decl())) {
                SASSERT(repl.size() == 2);
                if (repl[0] == repl[1]) return m.mk_true();
                if (m.is_value(repl[0]) && m.is_value(repl[1])) {
                    return m.mk_false();
                }
            }
            std::cout << "OPTIMIZE? " << orig->get_decl()->get_name().bare_str() << "[";
            for (unsigned i = 0; i < repl.size(); ++i) {
                if (i != 0)
                    std::cout << ", ";
                std::cout << mk_pp(repl[i], m);
            }
            std::cout << "]?" << std::endl;
            return m.mk_app(orig->get_decl(), repl.size(), repl.c_ptr());
        }
    }
    /* Check the interpreted tail for conflicts with the fixed variables.
       Returns false if a conflict exists. */
    bool mk_rule_exploder::check_tail() {
        ast_manager& m = m_context.get_manager();
        for (unsigned tail_pos = m_rule->get_uninterpreted_tail_size(); tail_pos < m_rule->get_tail_size(); ++tail_pos) {
            app* ntail = fix_app(m_rule->get_tail(tail_pos));
            if (ntail) {
                if (m_rule->is_neg_tail(tail_pos)) {
                    if (m.is_true(ntail)) {
                        return false;
                    }
                } else {
                    if (m.is_false(ntail)) {
                        return false;
                    }
                }
            }
        }
        return true;
    }
    /* Initialize the tail state. */
    void mk_rule_exploder::init_tail_state() {
        for (unsigned tail_pos = 0; tail_pos < m_rule->get_uninterpreted_tail_size(); ++tail_pos) {
            app* tail_el = m_rule->get_tail(tail_pos);
            tail_state& cur = m_tail_state[tail_pos];
            cur.m_fact = &m_engine->get_fact(tail_el->get_decl());
            //cur.m_instantiation.reset();
            for (unsigned arg_pos = 0; arg_pos < tail_el->get_num_args(); ++arg_pos) {
                expr* arg = tail_el->get_arg(arg_pos);
                expr* narg = fix_expr(arg);
                narg = narg ? narg : arg;
                const value_set& vs = cur.m_fact->get(arg_pos);
                if (vs.is_finite()) {
                    if (is_var(narg)) {
                        // The variable is not fixed, so we have to create an iteration for it
                        unsigned iter_pos = m_iters.size();
                        m_iters.push_back(iter_state(vs.get_values()));
                        m_fixed.insert(narg, fix_descr(iter_pos));
                        //cur.m_instantiation.push_back(*vs.get_values().begin());
                    } else {
                        //cur.m_instantiation.push_back(narg);
                    }
                }
            }
            //cur.m_decl = get_mapping(tail_el->get_decl(), cur.m_fact, cur.m_instantiation);
        }
    }
    /* Generate the next iteration state.
       Return false if no more states are available. */
    bool mk_rule_exploder::inc_iteration() {
        unsigned pos = 0;
        for (unsigned pos = 0; pos < m_iters.size(); ++pos) {
            iter_state& cur = m_iters[pos];
            if (++cur.m_cur != cur.m_end) {
                return true;
            }
            cur.m_cur = cur.m_begin;
        }
        return false;
    }
    func_decl* mk_rule_exploder::get_mapping(func_decl* orig, const argument_fact<value_set>& fact, vector<expr*>& inst) {
        mapping::entry* entry = m_mapping.insert_if_not_there2(orig, 0);
        inst_mapping* imap;
        if (entry->get_data().m_value) {
            imap = entry->get_data().m_value;
        } else {
            imap = entry->get_data().m_value = alloc(inst_mapping);
        }
        inst_mapping::entry* entry2 = imap->insert_if_not_there2(inst, 0);
        if (entry2->get_data().m_value == 0) {
            func_decl* new_decl;
            if (inst.empty()) {
                new_decl = orig;
            } else {
                vector<sort*> domain;
                for (unsigned i = 0; i < orig->get_arity(); ++i) {
                    if (!fact.get(i).is_finite()) {
                        domain.push_back(orig->get_domain(i));
                    }
                }
                SASSERT(orig->get_arity() == inst.size() + domain.size());
                new_decl = m_context.mk_fresh_head_predicate(orig->get_name(), symbol("expl"), domain.size(), domain.c_ptr(), orig);
            }
            entry2->get_data().m_value = new_decl;
            m_target->inherit_predicate(*m_source, orig, new_decl);
            m_todo.push_back(todo_entry(orig, new_decl, inst, fact));
            return new_decl;
        } else {
            return entry2->get_data().m_value;
        }
    }
    rule* mk_rule_exploder::make_rule(const todo_entry& cur) {
        // Generate the new head
        unsigned pos = 0;
        m_arg_cache.resize(cur.m_new->get_arity());
        for (unsigned head_pos = 0; head_pos < m_rule->get_head()->get_num_args(); ++head_pos) {
            const value_set& vs = cur.m_fact.get(head_pos);
            if (!vs.is_finite()) {
                expr* oarg = m_rule->get_head()->get_arg(head_pos);
                expr* narg = fix_expr(oarg);
                m_arg_cache[pos++] = narg ? narg : oarg;
            }
        }
        app* new_head = m_context.get_manager().mk_app(cur.m_new, m_arg_cache.size(), m_arg_cache.c_ptr());
        // Generate the new tail
        m_app_cache.resize(m_rule->get_tail_size());
        m_neg_cache.resize(m_rule->get_tail_size());
        for (unsigned tail_pos = m_rule->get_uninterpreted_tail_size(); tail_pos < m_rule->get_tail_size(); ++tail_pos) {
            app* tail_el = m_rule->get_tail(tail_pos);
            app* ntail_el = fix_app(tail_el);
            if (ntail_el) {
                if (m_rule->is_neg_tail(tail_pos)) {
                    if (m_context.get_manager().is_true(ntail_el)) {
                        return 0;
                    }
                } else {
                    if (m_context.get_manager().is_false(ntail_el)) {
                        return 0;
                    }
                }
                m_neg_cache[tail_pos] = m_rule->is_neg_tail(tail_pos);
                m_app_cache[tail_pos] = ntail_el;
            } else {
                m_neg_cache[tail_pos] = m_rule->is_neg_tail(tail_pos);
                m_app_cache[tail_pos] = tail_el;
            }
        }
        for (unsigned tail_pos = 0; tail_pos < m_rule->get_uninterpreted_tail_size(); ++tail_pos) {
            app* tail_el = m_rule->get_tail(tail_pos);
            tail_state& cur = m_tail_state[tail_pos];
            m_arg_cache.reset();
            m_inst_cache.reset();
            for (unsigned arg_pos = 0; arg_pos < tail_el->get_num_args(); ++arg_pos) {
                expr* oarg = tail_el->get_arg(arg_pos);
                expr* narg = fix_expr(oarg);
                const value_set& vs = cur.m_fact->get(arg_pos);
                if (vs.is_finite()) {
                    m_inst_cache.push_back(narg ? narg : oarg);
                } else {
                    m_arg_cache.push_back(narg ? narg : oarg);
                }
            }
            func_decl* ndecl = get_mapping(tail_el->get_decl(), *cur.m_fact, m_inst_cache);
            app* ntail_el = m_context.get_manager().mk_app(ndecl, m_arg_cache.size(), m_arg_cache.c_ptr());
            m_app_cache[tail_pos] = ntail_el;
            m_neg_cache[tail_pos] = m_rule->is_neg_tail(tail_pos);
        }
        return m_context.get_rule_manager().mk(new_head, m_app_cache.size(), m_app_cache.c_ptr(), m_neg_cache.c_ptr());
    }
    void mk_rule_exploder::get_iteration(vector<expr*>& inst) const {
        for (unsigned pos = 0; pos < m_iters.size(); ++pos) {
            inst[pos] = *m_iters[pos].m_cur;
        }
    }
    rule_set* mk_rule_exploder::operator()(rule_set const & source) {
        TRACE("mk_rule_exploder", tout << "Old rules:\n"; \
            for (rule_set::iterator it = source.begin(); it != source.end(); it++) {
                \
                    if (source.is_output_predicate((*it)->get_decl())) tout << "[O]"; (*it)->display(m_context, tout); \
            } tout.flush(););
        m_source = &source;
        m_target = alloc(rule_set, m_context);
        m_engine = alloc(value_set_engine,m_context.get_manager(), source);
        m_engine->run_bottom_up();
        m_todo.reset();
        const func_decl_set& outputs = source.get_output_predicates();
        for (func_decl_set::iterator I = outputs.begin(),
            E = outputs.end(); I != E; ++I) {
            const argument_fact<value_set>& output_fact = m_engine->get_fact(*I);
            m_iters.reset();
            for (unsigned pos = 0; pos < output_fact.size(); ++pos) {
                const value_set& vs = output_fact.get(pos);
                if (vs.is_finite()) {
                    m_iters.push_back(iter_state(vs.get_values()));
                }
            }
            m_inst_cache.resize(m_iters.size());
            get_iteration(m_inst_cache);
            get_mapping(*I, output_fact, m_inst_cache);
            while (inc_iteration()) {
                get_iteration(m_inst_cache);
                get_mapping(*I, output_fact, m_inst_cache);
            }
        }
        while (step());
        TRACE("mk_rule_exploder", tout << "New rules:\n"; \
            for (rule_set::iterator it = m_target->begin(); it != m_target->end(); it++) {
                \
                    if (m_target->is_output_predicate((*it)->get_decl())) tout << "[O]"; (*it)->display(m_context, tout); \
            });
        return m_target;
    }
    bool mk_rule_exploder::step() {
        if (m_todo.empty()) return false;
        todo_entry entr = m_todo.back();
        m_todo.pop_back();
        const rule_vector& rules = m_source->get_predicate_rules(entr.m_orig);
        for (unsigned pos_rule = 0; pos_rule < rules.size(); ++pos_rule) {
            rule* r = rules[pos_rule];
            set_rule(r);
            if (!get_fixed_head(entr)) continue;
            if (!check_tail()) continue;
            init_tail_state();
            do {
                rule* nrule = make_rule(entr);
                if (nrule) {
                    m_target->add_rule(nrule);
                }
            } while (inc_iteration());
        }
        return true;
    }
}
