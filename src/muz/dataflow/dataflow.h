/*++
Copyright (c) 2015 Microsoft Corporation

Module Name:

    dataflow.h

Abstract:

    Generic bottom-up and top-down data-flow engine for analysis
    of rule sets.

Author:
    Henning Guenther (t-hennig)

--*/

#ifndef DATAFLOW_H_
#define DATAFLOW_H_

#include "dl_rule.h"
#include "dl_rule_set.h"
#include "hashtable.h"
#include "vector.h"

namespace datalog {
    template <typename Fact> class fact_reader;
    template <typename Fact> class fact_setter;
    template <typename Fact> class fact_writer;
    /* The structure of fact classes:
    class fact {
    public:
        typedef ... ctx_t;
        // Empty fact
        static fact null_fact;
        fact(); -- needed because the facts are inserted into a hashtable. Should always be a no-op.
        fact(func_decl* symbol); -- bottom
        // Init (Top down)
        static void init_down(ctx_t& m, const rule_set& rules, fact_setter<fact>& setter);
        // Init (Bottom up)
        bool init_up(ctx_t& ctx, const rule* r);
        // Step (Bottom up)
        bool propagate_up(ctx_t& ctx, const rule* r, const fact_reader<fact>& tail_facts);
        // Step (Top down)
        void propagate_down(ctx_t& ctx, const rule* r, fact_writer<fact>& tail_facts) const;
        // Debugging
        void dump(ctx_t& ctx, std::ostream& outp) const;
        // Union
        void join(ctx_t& ctx, const Fact& oth);
        // Intersection
        void intersect(ctx_t& ctx, const Fact& oth);
    }; */
    template <typename Fact> class dataflow_engine {
    public:
        friend class fact_setter<Fact>;
        typedef map<func_decl*, Fact, obj_ptr_hash<func_decl>, ptr_eq<func_decl> > fact_db;
        typedef hashtable<func_decl*, obj_ptr_hash<func_decl>, ptr_eq<func_decl> > todo_set;
        typedef typename fact_db::iterator iterator;
    private:
        const rule_set& m_rules;
        fact_db m_facts;
        todo_set m_todo[2];
        unsigned m_todo_idx;
        typename Fact::ctx_t& m_context;
        rule_set::decl2rules m_body2rules;

        Fact& get_or_insert_fact(func_decl* sym) {
            typename fact_db::entry *entr;
            if (m_facts.insert_if_not_there_core(sym, Fact::null_fact, entr)) {
                // This is a new fact
                entr->get_data().m_value = Fact(sym);
            }
            return entr->get_data().m_value;
        }

        void init_bottom_up() {
            for (rule_set::iterator it = m_rules.begin(); it != m_rules.end(); ++it) {
                rule* cur = *it;
                func_decl *sym = cur->get_decl();
                for (unsigned i = 0; i < cur->get_uninterpreted_tail_size(); ++i) {
                    func_decl *d = cur->get_decl(i);
                    rule_set::decl2rules::obj_map_entry *e = m_body2rules.insert_if_not_there2(d, 0);
                    if (!e->get_data().m_value) {
                        e->get_data().m_value = alloc(ptr_vector<rule>);
                    }
                    e->get_data().m_value->push_back(cur);
                }
                bool new_info = get_or_insert_fact(sym).init_up(m_context, cur);
                if (new_info) {
                    m_todo[m_todo_idx].insert(sym);
                }
            }
        }

        void init_top_down() {
            fact_setter<Fact> setter(*this, false);
            Fact::init_down(m_context, m_rules, setter);
        }

        void step_bottom_up() {
            for(todo_set::iterator I = m_todo[m_todo_idx].begin(),
                E = m_todo[m_todo_idx].end(); I!=E; ++I) {
                ptr_vector<rule> * rules; 
                if (!m_body2rules.find(*I, rules))
                    continue;
                for (ptr_vector<rule>::iterator I2 = rules->begin(),
                    E2 = rules->end(); I2 != E2; ++I2) {
                    func_decl* head_sym = (*I2)->get_decl();
                    fact_reader<Fact> tail_facts(m_facts, *I2);
                    bool new_info = get_or_insert_fact(head_sym).propagate_up(m_context, *I2, tail_facts);
                    if (new_info) {
                        m_todo[!m_todo_idx].insert(head_sym);
                    }
                }
            }
            // Update todo list
            m_todo[m_todo_idx].reset();
            m_todo_idx = !m_todo_idx;
        }

        void step_top_down() {
            for(todo_set::iterator I = m_todo[m_todo_idx].begin(),
                E = m_todo[m_todo_idx].end(); I!=E; ++I) {
                func_decl *head_sym = *I;
                // We can't use a reference here because we are changing the map while using the reference
                const Fact head_fact = m_facts.get(head_sym, Fact::null_fact);
                const rule_vector& deps = m_rules.get_predicate_rules(head_sym);
                const unsigned deps_size = deps.size();
                for (unsigned i = 0; i < deps_size; ++i) {
                    rule *trg_rule = deps[i];
                    fact_writer<Fact> writer(*this, true, trg_rule);
                    // Generate new facts
                    head_fact.propagate_down(m_context, trg_rule, writer);
                }
            }
            // Update todo list
            m_todo[m_todo_idx].reset();
            m_todo_idx = !m_todo_idx;
        }

        bool done() const {
            return m_todo[m_todo_idx].empty();
        }

    public:
        dataflow_engine(typename Fact::ctx_t& ctx, const rule_set& rules) : m_rules(rules), m_todo_idx(0), m_context(ctx) {}

        ~dataflow_engine() {
            for (rule_set::decl2rules::iterator it = m_body2rules.begin(); it != m_body2rules.end(); ++it) {
                dealloc(it->m_value);
            }
        }

        void dump(std::ostream& outp) {
            obj_hashtable<func_decl> visited;
            for (rule_set::iterator I = m_rules.begin(),
                E = m_rules.end(); I != E; ++I) {
                const rule *r = *I;
                func_decl* head_decl = r->get_decl();
                obj_hashtable<func_decl>::entry *dummy;
                if (visited.insert_if_not_there_core(head_decl, dummy)) {
                    const Fact& fact = m_facts.get(head_decl, Fact::null_fact);
                    outp << head_decl->get_name() << " -> ";
                    fact.dump(m_context, outp);
                    outp << "\n";
                }
                for (unsigned i = 0; i < r->get_uninterpreted_tail_size(); ++i) {
                    func_decl *tail_decl = r->get_decl(i);
                    if (visited.insert_if_not_there_core(tail_decl, dummy)) {
                        const Fact& fact = m_facts.get(tail_decl, Fact::null_fact);
                        outp << tail_decl->get_name() << " -> ";
                        fact.dump(m_context, outp);
                        outp << "\n";
                    }
                }
            }
        }

        void run_bottom_up() {
            init_bottom_up();
            while (!done()) step_bottom_up();
        }

        void run_top_down() {
            init_top_down();
            while (!done()) step_top_down();
        }

        const Fact& get_fact(func_decl* decl) const {
            return m_facts.get(decl, Fact::null_fact);
        }

        const fact_db& get_facts() const { return m_facts; }
        iterator begin() const { return m_facts.begin(); }
        iterator end() const { return m_facts.end(); }

        void join(const dataflow_engine<Fact>& oth) {
            for (typename fact_db::iterator I = oth.m_facts.begin(),
                E = oth.m_facts.end(); I != E; ++I) {
                typename fact_db::entry* entry;
                if (m_facts.insert_if_not_there_core(I->m_key, entry)) {
                    entry->get_data().m_value = I->m_value;
                } else {
                    entry->get_data().m_value.join(m_context, I->m_value);
                }
            }
        }

        void intersect(const dataflow_engine<Fact>& oth) {
            vector<func_decl*> to_delete;
            for (typename fact_db::iterator I = m_facts.begin(),
                E = m_facts.end(); I != E; ++I) {
                
                if (typename fact_db::entry *entry = oth.m_facts.find_core(I->m_key)) {
                    I->m_value.intersect(m_context, entry->get_data().m_value);
                } else {
                     to_delete.push_back(I->m_key);
                }
            }
            for (unsigned i = 0; i < to_delete.size(); ++i) {
                m_facts.erase(to_delete[i]);
            }
        }
    };

    // This helper-class is used to look up facts for rule tails
    template <typename Fact> class fact_reader {
        typedef typename dataflow_engine<Fact>::fact_db fact_db;
        const fact_db& m_facts;
        const rule* m_rule;
    public:
        fact_reader(const fact_db& facts, const rule* r)
            : m_facts(facts), m_rule(r) {

        }
        const Fact& get(unsigned idx) const {
            return m_facts.get(m_rule->get_decl(idx), Fact::null_fact);
        }
        unsigned size() const {
            return m_rule->get_uninterpreted_tail_size();
        }
    };
    
    template <typename Fact> class fact_setter {
        friend class dataflow_engine<Fact>;
        dataflow_engine<Fact>& m_facts;
        unsigned m_todo_idx;
    public:
        fact_setter(dataflow_engine<Fact>& facts, bool insert_into_next = false) : m_facts(facts), m_todo_idx(insert_into_next ? !facts.m_todo_idx : facts.m_todo_idx) {}

        Fact& get(func_decl* sym) {
            return m_facts.get_or_insert_fact(sym);
        }

        void set_changed(func_decl* sym) {
            m_facts.m_todo[m_todo_idx].insert(sym);
        }
    };
    
    template <typename Fact> class fact_writer : public fact_setter<Fact> {
        const rule* m_rule;
    public:
        fact_writer(dataflow_engine<Fact>& facts, bool insert_into_next, const rule* r) : fact_setter<Fact>(facts, insert_into_next), m_rule(r) {}

        Fact& get(unsigned idx) {
            func_decl *sym = m_rule->get_decl(idx);
            return fact_setter<Fact>::get(sym);
        }

        void set_changed(unsigned idx) {
            fact_setter<Fact>::set_changed(m_rule->get_decl(idx));
        }

        unsigned size() const {
            return m_rule->get_uninterpreted_tail_size();
        }
    };
}

#endif
