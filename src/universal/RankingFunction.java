import java.util.Set;
import java.util.Vector;

public class RankingFunction
{
    public static int cCount = 0, sCount = 0, tCount=0, lCount=0;
    public static Vector<String> nonNegativeLvars = new Vector<>();


    public static void MakeTemplate()
    {
        for (CFGNode n : CFGNode.allCFGNodes)
        {
            if(!n.isCutPoint)
                continue;
            Polynomial rank = new Polynomial(); // c_0 * 1 + c_1 * m_1 + c_2 * m_2 .... + c_n * m_n >=0
            Set<Monomial> allMonomials= Monomial.getAllMonomials(Parser.allVars,Main.degree);
            for (Monomial m : allMonomials)
            {
                m.addVar("c_"+cCount,1);
                rank.add(m,Rational.one); // p+= var * c_cCount
                cCount++;
            }
            n.rank = rank;

            Polynomial inv = new Polynomial();  // s_0 * 1 + s_1 * var_1 + s_2 * var2 .... + s_n * var_n >=0
            allMonomials= Monomial.getAllMonomials(Parser.allVars,Main.degree);
            for (Monomial m : allMonomials)
            {
                m.addVar("s_"+sCount,1);
                inv.add(m,Rational.one); // p+= var * c_cCount
                sCount++;
            }
            n.inv = inv;

        }
    }


    public static void generate(Vector<Putinar> putinarVector)
    {

        //invariant for Main.startNode:
        Putinar startInv = new Putinar(-1, Main.startNode.id);
        startInv.addPredicate(Main.pre_condition);
        startInv.setObjective(Main.startNode.inv);
        putinarVector.add(startInv);

        // ranking function for Main.startNode:
        Putinar startRank = new Putinar(-1, Main.startNode.id);
        startRank.addPredicate(Main.pre_condition);
        startRank.setObjective(Main.startNode.rank);
        putinarVector.add(startRank);

        for(CFGNode v:CFGNode.allCFGNodes)
            if(v.isCutPoint)
                processPaths(v,new Vector<Transition>(),putinarVector);
    }
//
    public static void addFarkas(Transition t, Vector<Putinar> putinarVector)
    {
        // Invariant:

        Putinar finv = new Putinar(t.from.id, t.to.id);
        finv.addPredicate(t.detGuard.deepCopy());
        finv.addPredicate(t.from.pre_condition);
        finv.addPredicate(new PolynomialPredicate(t.from.inv.deepCopy()));
        Polynomial qinv = t.to.inv.deepCopy();
        qinv.replaceVarsWithPoly(t.varName,t.update);
        finv.setObjective(qinv);
        putinarVector.add(finv);

        // Ranking function:
        if(t.from.isBuchi || t.to.isBuchi)          //TODO: check heuristic
        {
            Putinar f = new Putinar(t.from.id,t.to.id);
            f.addPredicate(t.detGuard.deepCopy());
            f.addPredicate(t.from.pre_condition);
            PolynomialPredicate qp = new PolynomialPredicate();
            qp.add(t.from.rank.deepCopy());
            qp.add(t.from.inv.deepCopy());
            f.addPredicate(qp);

            Polynomial qc = t.to.rank.deepCopy();
            qc.replaceVarsWithPoly(t.varName,t.update);
            f.setObjective(qc);
            putinarVector.add(f);
        }
        else
        {
            Putinar f1= new Putinar(t.from.id,t.to.id);
            f1.addPredicate(t.detGuard.deepCopy());
            f1.addPredicate(t.from.pre_condition);
            PolynomialPredicate qp = new PolynomialPredicate();
            qp.add(t.from.rank.deepCopy());
            qp.add(t.from.inv.deepCopy());
            f1.addPredicate(qp);
            Polynomial qc1 = t.to.rank.deepCopy();
            qc1.replaceVarsWithPoly(t.varName,t.update);
            f1.setObjective(qc1);
            putinarVector.add(f1);

            Putinar f2 = new Putinar(t.from.id, t.to.id);
            f2.addPredicate(t.detGuard.deepCopy());
            f2.addPredicate(t.from.pre_condition);
            f2.addPredicate(qp.deepCopy());

            Polynomial qc2 = t.from.rank.deepCopy();
            qc2.add(Monomial.one,Rational.negate(Rational.one));
            Polynomial qc3 = t.to.rank.deepCopy();
            qc3.replaceVarsWithPoly(t.varName,t.update);

            qc2.add(qc3.negate());
            f2.setObjective(qc2);
            putinarVector.add(f2);
        }
    }
    // processPaths: uses dfs to generate a farkas for every path outgoing from the starting node
    private static void processPaths(CFGNode v, Vector<Transition> path, Vector<Putinar> putinarVector)
    {
        Vector<Transition> tran=v.out;

        for(Transition t:tran)
        {
            CFGNode u=t.to;
            path.add(t);


            if(u.isCutPoint)
            {
                Transition tau = CFGUtil.weakestPreCondition(path);
                addFarkas(tau, putinarVector);
            }
            else
                processPaths(u,path,putinarVector);
            path.removeElementAt(path.size()-1);
        }
    }



}