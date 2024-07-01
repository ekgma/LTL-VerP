import java.util.Vector;

public class DNFPoly
{
    private Vector<PolynomialPredicate> clauses;
    DNFPoly()
    {
        clauses = new Vector<>();
    }

    public void or(PolynomialPredicate lp)
    {
        for(PolynomialPredicate clause: clauses)
            if(lp.equalsLogic(clause))
                return;
        clauses.add(lp);
    }

    public void or(Polynomial lc)
    {
        this.or(new PolynomialPredicate(lc));
    }

    public void or(DNFPoly dnf)
    {
        for(PolynomialPredicate lp: dnf.getClauses())
            this.or(lp);
    }

    public void and(PolynomialPredicate lp)
    {
        for(PolynomialPredicate clause: clauses)
            clause.add(lp);
    }

    public void and(Polynomial lc) // lc >= 0
    {
        for (PolynomialPredicate clause : clauses)
            clause.add(lc);
    }

    public void and(DNFPoly dnf)
    {
        Vector<PolynomialPredicate> res = new Vector<>();
        for(PolynomialPredicate lp: dnf.getClauses())
            for(PolynomialPredicate clause: clauses)
            {
                PolynomialPredicate tmp = clause.deepCopy();
                tmp.add(lp.deepCopy());
                res.add(tmp);
            }
        clauses=res;
    }

    public DNFPoly negate()
    {
        DNFPoly ret = null;
        if(clauses.isEmpty())
            return new DNFPoly();
        for(PolynomialPredicate clause: clauses)
        {
            DNFPoly neg = clause.negate();
            if(ret == null)
                ret = neg;
            else
                ret.and(neg);
        }
        return ret;
    }

    public void replaceVarsWithPoly(Vector<String> vars, Vector<Polynomial> upd)
    {
        for(PolynomialPredicate pp: clauses)
            pp.replaceVarsWithPoly(vars,upd);
    }

    public int size()
    {
        return clauses.size();
    }
    public Vector<PolynomialPredicate> getClauses()
    {
        return clauses;
    }

    public DNFPoly deepCopy()
    {
        DNFPoly ret = new DNFPoly();
        for(PolynomialPredicate clause: clauses)
            ret.or(clause.deepCopy());
        return ret;
    }

    public String toString()
    {
        if(clauses.isEmpty())
            return "[empty]";
        String ret = "[ ";
        for(PolynomialPredicate clause: clauses)
            ret +="( "+clause.toNormalString()+" ) or ";
        ret=ret.substring(0,ret.length()-3)+"]";
        return ret;
    }

    public String toSMT()
    {
        if(clauses.isEmpty())
            return "(>= 1 0)";
        if(clauses.size()==1)
            return clauses.firstElement().toSMT();
        else
        {
            String ret ="(or ";
            for(PolynomialPredicate pp: clauses)
                ret+= pp.toSMT()+" ";
            ret+=")";
            return ret;
        }
    }
}
