/* 
A helper class to construct facts that talk about variables instead of predicates.
*/
#ifndef DATAFLOW_ARG_H_
#define DATAFLOW_ARG_H_

#include "dataflow.h"
#include "vector.h"
#include "bit_vector.h"

namespace datalog {
    template<typename Fact> class var_facts;

    template<typename Fact> class argument_fact {
        vector<Fact> m_facts;
    public:
        typedef typename Fact::ctx_t ctx_t;
        static argument_fact<Fact> null_fact;
        argument_fact() {}
        argument_fact(func_decl* decl) : m_facts(decl->get_arity()) {

        }
        const Fact& get(unsigned idx) const {
            if (idx < m_facts.size()) {
                return m_facts[idx];
            } else {
                return Fact::null_fact;
            }
        }

        bool init_down(ctx_t& ctx, const rule* r) {
            const app* head = r->get_head();
            bool changed = false;
            for (unsigned i = 0; i < head->get_num_args(); ++i) {
                const expr* arg = head->get_arg(i);
                changed |= m_facts[i].init_down(ctx, arg);
            }
            return changed;
        }

        bool init_up(ctx_t& ctx, const rule* r) {
            bool changed = false;
            for (unsigned i = 0; i < r->get_head()->get_num_args(); ++i) {
                expr* head_arg = r->get_head()->get_arg(i);
                changed |= m_facts[i].init_up(ctx, head_arg);
            }
            return changed;
        }

        bool propagate_up(ctx_t& ctx, const rule* r, const fact_reader<argument_fact<Fact> >& tail_facts) {
            var_facts<Fact> derived(ctx, r, tail_facts);
            Fact::inference(ctx, derived, r);
            bool changed = false;
            for (unsigned i = 0; i < r->get_head()->get_num_args(); ++i) {
                expr* head_arg = r->get_head()->get_arg(i);
                if (is_var(head_arg)) {
                    changed |= m_facts[i].join(ctx, derived.get(to_var(head_arg)->get_idx()));
                } else {
                    changed |= m_facts[i].join_constant(ctx, head_arg);
                }
            }
            return changed;
        }

        void propagate_down(ctx_t& ctx, const rule* r, fact_writer<argument_fact<Fact> >& tail_facts) const {
            var_facts<Fact> derived(ctx, r, *this);
            const unsigned unint_size = r->get_uninterpreted_tail_size();
            Fact::inference(derived, r->get_tail(unint_size), r->get_tail_size() - unint_size);
            for (unsigned i = 0; i < r->get_uninterpreted_tail_size(); ++i) {
                const app* tail_el = r->get_tail(i);
                bool changed = false;
                const argument_fact<Fact>& tail_fact = tail_facts.get(i);
                for (unsigned j = 0; j < tail_el->get_num_args(); ++j) {
                    if (is_var(tail_el->get_arg(j))) {
                        changed |= tail_fact.m_facts[j].join(ctx, derived.get(to_var(tail_el->get_arg(j))->get_idx()));
                    } else {
                        changed |= tail_fact.m_facts[j].join_constant(ctx, tail_el->get_arg(j));
                    }
                }
                if (changed) tail_facts.set_changed(i);
            }
        }

        void dump(ctx_t& ctx, std::ostream& outp) const {
            outp << "[";
            for (unsigned i = 0; i < m_facts.size(); ++i) {
                if (i > 0) outp << ",";
                m_facts[i].dump(ctx, outp);
            }
            outp << "]";
        }
        void join(ctx_t& ctx, const argument_fact<Fact>& oth) {
            for (unsigned i = 0; i < m_facts.size(); ++i) {
                m_facts[i].join(ctx, oth.m_facts[i]);
            }
        }
        void intersect(ctx_t& ctx, const argument_fact<Fact>& oth) {
            for (unsigned i = 0; i < m_facts.size(); ++i) {
                m_facts[i].intersect(ctx, oth.m_facts[i]);
            }
        }
        unsigned size() const {
            return m_facts.size();
        }
        void deref(ctx_t& ctx) {
            for (unsigned i = 0; i < m_facts.size(); ++i) {
                m_facts[i].deref(ctx);
            }
        }
    };

    template<typename Fact> argument_fact<Fact> argument_fact<Fact>::null_fact = argument_fact<Fact>();


    template<typename Fact> class var_facts {
        vector<Fact> m_facts;
        typename Fact::ctx_t& m_ctx;
        void set(unsigned idx, const Fact& oth) {
            m_facts.reserve(idx+1, Fact::full_fact);
            m_facts[idx].intersect(m_ctx, oth);
        }
    public:
        var_facts(typename Fact::ctx_t& ctx, const rule* r, const fact_reader<argument_fact<Fact> >& reader) : m_ctx(ctx) {
            for (unsigned i = 0; i < r->get_uninterpreted_tail_size(); ++i) {
                const app* tail_el = r->get_tail(i);
                const argument_fact<Fact>& tail_fact = reader.get(i);
                for (unsigned j = 0; j < tail_el->get_num_args(); ++j) {
                    const expr* arg = tail_el->get_arg(j);
                    if (is_var(arg)) {
                        set(to_var(arg)->get_idx(), tail_fact.get(j));
                    }
                }
            }
        }
        var_facts(typename Fact::ctx_t& ctx, const rule* r, const argument_fact<Fact>& head_facts) : m_ctx(ctx) {
            for (unsigned i = 0; i < r->get_head()->get_num_args(); ++i) {
                const expr* arg = r->get_head()->get_arg(i);
                if (is_var(arg)) {
                    set(to_var(arg)->get_idx(), head_facts.get(i));
                }
            }
        }
        Fact& get(unsigned idx) {
            if (idx >= m_facts.size()) {
                m_facts.resize(idx + 1,Fact::full_fact);
            }
            return m_facts[idx];
        }
    };
}

#endif
