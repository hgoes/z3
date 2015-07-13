#include "value_set.h"
#include "var_subst.h"

namespace datalog {
    value_set::value_set(bool any) : m_any_value(any) {

    }
    value_set value_set::null_fact = value_set();
    value_set value_set::full_fact = value_set(true);
    void value_set::inference(ctx_t& ctx, var_facts<value_set>& facts, const rule* r) {
#if 0
        expr_free_vars fv;
        for (unsigned i = r->get_uninterpreted_tail_size(); i < r->get_tail_size(); ++i) {
            fv.accumulate(r->get_tail(i));
        }
        for (unsigned i = 0; i < fv.size(); ++i) {
            if (fv[i]) {
                value_set& vals = facts.get(i);
                if (!vals.m_any_value) {
                    vals.m_values.reset();
                    vals.m_any_value = true;
                }
            }
        }
#endif
    }

    bool value_set::init_up(ctx_t& ctx, expr* arg) {
        if (is_var(arg)) {
            if (m_any_value)
                return false;
            else {
                m_any_value = true;
                m_values.reset();
                return true;
            }
        } else {
            obj_hashtable<expr>::entry* dummy;
            if (m_any_value)
                return false;
            else if (m_values.insert_if_not_there_core(arg, dummy))
                return true;
            else
                return false;
        }
    }
    void value_set::init_down(ctx_t& m, const rule_set& rules, fact_setter<value_set>& setter) {
#if 0
        if (is_var(arg)) {
            if (m_any_value)
                return false;
            else {
                m_any_value = true;
                m_values.reset();
                return true;
            }
        } else {
            obj_hashtable<expr>::entry* dummy;
            if (m_any_value)
                return false;
            else if (m_values.insert_if_not_there_core(arg, dummy))
                return true;
            else
                return false;
        }
#endif
    }

    bool value_set::join(ctx_t& ctx, const value_set& oth) {
        if (m_any_value) return false;
        if (oth.m_any_value) {
            for (obj_hashtable<expr>::iterator I = m_values.begin(),
                E = m_values.end(); I != E; ++I) {
                //ctx.dec_ref(*I);
            }
            m_values.reset();
            m_any_value = true;
            return true;
        }
        bool new_value = false;
        for (obj_hashtable<expr>::iterator I = oth.m_values.begin(),
            E = oth.m_values.end(); I != E; ++I) {
            obj_hashtable<expr>::entry* entry;
            if (m_values.insert_if_not_there_core(*I, entry)) {
                //ctx.inc_ref(*I);
                new_value = true;
            }
        }
        return new_value;
    }
    bool value_set::join_constant(ctx_t& ctx, expr* value) {
        obj_hashtable<expr>::entry* entry;
        if (m_values.insert_if_not_there_core(value, entry)) {
            //ctx.inc_ref(value);
            return true;
        } else {
            return false;
        }
    }
    bool value_set::intersect(ctx_t& ctx, const value_set& oth) {
        if (oth.m_any_value) return false;
        if (m_any_value) {
            m_any_value = false;
            for (obj_hashtable<expr>::iterator I = oth.m_values.begin(),
                E = oth.m_values.end(); I != E; ++I) {
                m_values.insert(*I);
                //ctx.inc_ref(*I);
            }
            return true;
        }
        bool changed = false;
        vector<expr*> to_delete;
        for (obj_hashtable<expr>::iterator I = m_values.begin(),
            E = m_values.end(); I != E; ++I) {
            if (!oth.m_values.contains(*I)) {
                changed = true;
                to_delete.push_back(*I);
            }
        }
        for (unsigned i = 0; i < to_delete.size(); ++i) {
            //ctx.dec_ref(to_delete[i]);
            m_values.erase(to_delete[i]);
        }
        return changed;
    }
    void value_set::dump(ctx_t& ctx, std::ostream& outp) const {
        if (m_any_value) {
            outp << "any";
        } else {
            outp << "{";
            for (obj_hashtable<expr>::iterator S = m_values.begin(),
                I=S,
                E = m_values.end(); I != E; ++I) {
                if (I != S) outp << ",";
                outp << mk_pp(*I, ctx);
            }
            outp << "}";
        }
    }
    bool value_set::is_finite() const {
        return !m_any_value;
    }
    const obj_hashtable<expr>& value_set::get_values() const {
        SASSERT(!m_any_value);
        return m_values;
    }
    void value_set::deref(ctx_t& ctx) {
        for (obj_hashtable<expr>::iterator I = m_values.begin(),
            E = m_values.end(); I != E; ++I) {
            //ctx.dec_ref(*I);
        }
    }
}
