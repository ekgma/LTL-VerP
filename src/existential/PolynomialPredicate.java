import java.io.FileWriter;
import java.util.Collection;
import java.util.Vector;

public class PolynomialPredicate
{
    Vector<Polynomial> exprs;
    public static PolynomialPredicate TRUE = new PolynomialPredicate(new Polynomial(Monomial.one));

    PolynomialPredicate()
    {
        exprs = new Vector<>();
    }

    PolynomialPredicate(Polynomial poly)
    {
        exprs = new Vector<>();
        add(poly);
    }

    void add(Polynomial poly)
    {
        for (Polynomial p : exprs)
            if (p.equals(poly))
                return;
        exprs.add(poly);
    }

    void addAll(Collection<Polynomial> collection)
    {
        for(Polynomial poly: collection)
            add(poly);
    }
    public int degree()
    {
        int ret =0;
        for(Polynomial p: exprs)
            ret = Integer.max(ret, p.degree());
        return ret;
    }

    public Vector<PolynomialPredicate> subPredicates()
    {
        Vector<PolynomialPredicate> ret = new Vector<>();
        int sz = exprs.size();
        for (int i = 0; i < (1 << sz); i++)
        {
            PolynomialPredicate lp = new PolynomialPredicate();
            for (int j = 0; j < sz; j++)
                if ((i & (1 << j)) != 0)
                    lp.add(exprs.elementAt(j).deepCopy());
                else
                {
                    Polynomial lc = exprs.elementAt(j).negate();
                    lc.add(Monomial.one, Rational.negate(Rational.one));
                    lp.add(lc);
                }
            ret.add(lp);
        }
        return ret;
    }

    void add(PolynomialPredicate pp)
    {
        for (Polynomial poly : pp.exprs)
            add(poly.deepCopy());
    }

    void replaceVar(String var, String sub)
    {
        for(Polynomial poly: exprs)
            poly.replaceVarWithPoly(var, new Polynomial(sub));
    }

    void replaceVarsWithPoly(Vector<String> vars, Vector<Polynomial> upd)
    {
        for(Polynomial p: exprs)
            p.replaceVarsWithPoly(vars,upd);
    }

    public DNFPoly negate()
    {
        DNFPoly ret = new DNFPoly();
        for (Polynomial poly : exprs)
        {
            Polynomial p = poly.negate();
            p.add(Monomial.one, Rational.negate(Main.eps));
            PolynomialPredicate pp = new PolynomialPredicate();
            pp.add(p);
            ret.or(pp);
        }
        return ret;
    }

    public static DNFPoly negate(Vector<PolynomialPredicate> g, int first)
    {
        if (first == g.size())
            return new DNFPoly();
        else if (first == g.size() - 1)
            return g.elementAt(first).negate();
        else
        {
//            Vector<PolynomialPredicate> ret = new Vector<>();
            DNFPoly notFirst = g.elementAt(first).negate();
            DNFPoly recurse = negate(g, first + 1);
//            for (PolynomialPredicate pp : notFirst)
//                for (PolynomialPredicate predicate : recurse)
//                {
//                    PolynomialPredicate copy = predicate.deepCopy();
//                    copy.add(pp);
//                    ret.add(copy);
//                }
            notFirst.and(recurse);
            return notFirst;
        }
    }




    boolean equalsLogic(PolynomialPredicate pp)
    {
        for (Polynomial p : exprs)
            if (!pp.contains(p))
                return false;
        for (Polynomial p : pp.exprs)
            if (!this.contains(p))
                return false;
        return true;
    }

    boolean contains(Polynomial p)
    {
        for (Polynomial poly : exprs)
            if (p.equals(poly))
                return true;
        return false;
    }

    public boolean contains(PolynomialPredicate lp)
    {
        for(Polynomial lc: lp.exprs)
            if(!contains(lc))
                return false;
        return true;
    }

    PolynomialPredicate deepCopy()
    {
        PolynomialPredicate ret = new PolynomialPredicate();
        ret.add(this);
        return ret;
    }

    public String toNormalString()
    {
        String ret = "";
        for (int i = 0; i < exprs.size(); i++)
        {
            Polynomial p = exprs.elementAt(i);
            if (i == 0)
                ret += p.toNormalString() + ">=0";
            else
                ret += " && " + p.toNormalString() + ">=0";
        }
        return ret;
    }

    public boolean isSAT() throws Exception
    {
//        System.err.println("checking sat of: "+ toNormalString());
        String smt = "(set-option :print-success false)\n";
        smt += "(set-option :produce-models true)\n" +
                "(set-option :produce-assertions true)\n" +
                "(set-logic QF_NIA)\n";
//        System.err.println("here: "+toString());
        for(String var: Parser.allVars)
            if(!var.equals("1"))
                smt += "(declare-const "+var+ " Int )\n";
        for(Polynomial lc: exprs)
            smt+="(assert (>= "+ lc.toSMT()+" 0))\n";
        smt+="(check-sat)";
        FileWriter fw = new FileWriter(Main.workingdir + "/" + Main.solver + Main.fileName+ Main.varType + "_tmp.smt2");
        fw.write(smt);
        fw.close();
        Vector<String> core = InvUtil.check("z3", Main.workingdir + "/" + Main.solver + Main.fileName+Main.varType + "_tmp.smt2",1800);
        return !core.isEmpty() && core.firstElement().equals("True");
    }

    public String toNormalString_linear()
    {
        String ret = "";
        Polynomial one = new Polynomial(Rational.one);
        for (int i = 0; i < exprs.size(); i++)
        {
            Polynomial p = exprs.elementAt(i);
            if(p.degree()>1)
                continue;
            if(p.equals(one))
                continue;
            if (ret.equals(""))
                ret += p.toNormalString() + ">=0";
            else
                ret += " && " + p.toNormalString() + ">=0";
        }
        if(ret.equals(""))
            ret = " 1 >= 0";
        return ret;
    }

    public String toSMT()
    {
        if(exprs.isEmpty())
            return "(>= 1 0)";
        else if(exprs.size()==1)
            return "(= 0 "+exprs.firstElement().toSMT()+")";
        else
        {
            String ret = "(and ";
            for(Polynomial poly: exprs)
                ret+= "(= 0 "+poly.toSMT()+") ";
            ret+=")";
            return ret;
        }
    }
}