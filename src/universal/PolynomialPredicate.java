
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

    void add(PolynomialPredicate pp)
    {
        for (Polynomial poly : pp.exprs)
            add(poly.deepCopy());
    }

    void addAll(Collection<Polynomial> collection)
    {
        for (Polynomial poly : collection)
            add(poly);
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

    PolynomialPredicate deepCopy()
    {
        PolynomialPredicate ret = new PolynomialPredicate();
        ret.add(this);
        return ret;
    }

    public int degree()
    {
        int ret =0;
        for(Polynomial p: exprs)
            ret = Integer.max(ret, p.degree());
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