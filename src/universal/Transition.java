import java.util.Vector;

public class Transition    //from "v.first" to "v.second" with guard "g" and update "varName := update"
{
    public static Vector<Transition> allTransitions = new Vector<>();
    CFGNode from, to;
    PolynomialPredicate detGuard;

    Vector<String> varName;
    Vector<Polynomial> update;
    boolean hasGroup;

    Transition(CFGNode a, CFGNode b)
    {
        from = a;
        to = b;
        detGuard = new PolynomialPredicate();
        varName = new Vector<>();
        update = new Vector<>();
        hasGroup = false;
    }

    public void addToGraph()
    {
        allTransitions.add(this);
        from.out.add(this);
    }


    public void replaceVarsWithPoly(Vector<String> vars, Vector<Polynomial> upd)
    {
        detGuard.replaceVarsWithPoly(vars,upd);
        for(Polynomial lc: update)
            lc.replaceVarsWithPoly(vars,upd);
    }

    public Transition deepCopy()
    {
        Transition ret = new Transition(from, to);
        ret.detGuard = detGuard.deepCopy();
        ret.varName.addAll(varName);
        for (Polynomial lc : update)
            if (lc != null)
                ret.update.add(lc.deepCopy());
            else
                ret.update.add(null);
        return ret;
    }

    public String toString()
    {
        String res = "";
        res += "from: " + from.id + "\nto: " + to.id + "\n";
        if (detGuard != null)
            res += "detGuard: " + detGuard.toNormalString() + "\n";
        for (int i = 0; i < varName.size(); i++)
            if (update.elementAt(i) != null)
                res += varName.elementAt(i) + " := " + update.elementAt(i).toNormalString() + "\n";
            else
                res += varName.elementAt(i) + " := nondet()\n";
        return res;
    }
}