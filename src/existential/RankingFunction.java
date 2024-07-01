import java.util.Map;
import java.util.Set;
import java.util.TreeMap;
import java.util.Vector;

public class RankingFunction
{
    public static int cCount = 0, sCount = 0, tCount= 0 , lCount=0;
    public static Vector<String> nonNegativeLvars= new Vector<>();
    public static Map<String,String> varSubs = new TreeMap<>();

    public static void MakeTemplate()
    {
//        Main.startNode.inv = new Polynomial("1", new LinearCombination(Rational.one));
        cCount =sCount =tCount= lCount=0;
        nonNegativeLvars.clear();;
        varSubs.clear();

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
        for(String var: Parser.allVars)
            if(!var.equals("1"))
                varSubs.put(var,"p_"+var);
    }

    public static void addInitialPutinar(Vector<Putinar> putinarVector, PolynomialPredicate pre_condition)
    {
        Putinar putinarInv = new Putinar(-1,Main.startNode.id);
        putinarInv.addPredicate(pre_condition);
        putinarInv.setObjective(Main.startNode.inv);
        putinarVector.add(putinarInv);
    }
    public static void generate(Vector<Putinar> putinarVector, PolynomialPredicate pre_condition) throws Exception
    {
        addInitialPutinar(putinarVector, pre_condition);
        for(CFGNode v:CFGNode.allCFGNodes)
        {
            Vector<Transition> cutPointTransitions = new Vector<>();
            if (v.isCutPoint)
                processPaths(v, new Vector<>(), cutPointTransitions);
            //cutPointTransitions is the vector of all transitions outgoing from v
            addPutinar(v, cutPointTransitions, putinarVector);
        }
    }

    public static void addPutinar(CFGNode v, Vector<Transition> transitions, Vector<Putinar> putinarVector) throws Exception
    {
        // 0) generate invariants:
        for (Transition tau : transitions)
        {
            Putinar putinar = new Putinar(v.id, tau.to.id);
            putinar.addPredicate(new PolynomialPredicate(v.inv));
            putinar.addPredicate(tau.detGuard);
            putinar.addPredicate(v.pre_condition);
            Polynomial qc = tau.to.inv.deepCopy();
            qc.replaceVarsWithPoly(tau.varName, tau.update);
            putinar.setObjective(qc);
            putinarVector.add(putinar);
        }
        // v -> u_1 , u_2, ... , u_n
        // 1) get union G of all guards in "transitions"
        // 2) for every subset A of G:
        // 2.1) check satisfiability of A & ~(A^c)
        // 2.2) if SAT -> generate putinar for enabled transitions
        // NOTE: a transition is enabled iff its guard is a subset of A

        // 1)
        PolynomialPredicate G = new PolynomialPredicate();
        for(Transition tau: transitions)
            G.add(tau.detGuard.deepCopy());
        // 2)
        Vector<PolynomialPredicate> subs = G.subPredicates();
        for(PolynomialPredicate lp: subs)
            if(lp.isSAT())                                              // 2.1
            {
                Vector<Transition> en = enabled(transitions, lp);       // 2.2
                if(!en.isEmpty())
                    addRankingPutinar(v, en, lp, putinarVector);                     // 2.2
            }
    }

    public static Vector<Transition> enabled(Vector<Transition> transitions, PolynomialPredicate lp)
    {
        Vector<Transition> ret = new Vector<>();
        for(Transition tau: transitions)
            if(lp.contains(tau.detGuard))
                ret.add(tau);
        return ret;
    }



    public static void addRankingPutinar(CFGNode v, Vector<Transition> en, PolynomialPredicate lp,  Vector<Putinar> putinarVector) throws Exception
    {
        if(v.isBuchi)
        {
            //if lp && f(v)>=0 && f(u_1)<0 && f(u_2) <0 && ... && f(u_{n-1})<0 -> f(u_n)>=0
            Putinar putinar = new Putinar(v.id, en.lastElement().to.id);
            putinar.addPredicate(lp);
            putinar.addPredicate(v.pre_condition);
            putinar.addPredicate(new PolynomialPredicate(v.rank));
            putinar.addPredicate(new PolynomialPredicate(v.inv));
            for(Transition tau: en)
            {
                if(tau==en.lastElement())
                    continue;
                Polynomial qc = nonNegativity(tau).exprs.firstElement();      // f(u_i) >= 0
                qc = qc.negate();
                qc.add(new Polynomial(Rational.negate(Rational.one)));           // -f(u_i) - 1 >=0   -> f(u_i) < 0
                putinar.addPredicate(new PolynomialPredicate(qc));
            }
            putinar.setObjective(nonNegativity(en.lastElement()).exprs.firstElement());
            putinarVector.add(putinar);
        }
        else
        {
            //if lp && f(v)>=0 && ~rank(v,u_1) && ~rank(v,u_2) && ... && ~rank(v, u_{n-1}) -> rank(v, u_n)
            DNFPoly dnf = new DNFPoly();
//            dnf.or(lp.toQuadratic());
            dnf.or(v.rank);
            for(Transition tau: en)
            {
                if(tau==en.lastElement())
                    continue;

                DNFPoly tmp = new DNFPoly();
                tmp.or(rank(tau));              // tau is ranked
                tmp.and(nonNegativity(tau));    // destination is non-negative
                dnf.and(tmp.negate());          // negation is added to dnf
            }

            Vector<PolynomialPredicate> clauses = dnf.getClauses();
            for(PolynomialPredicate qc: clauses)
            {
                Putinar putinar1 = new Putinar(v.id, en.lastElement().to.id);
                putinar1.addPredicate(lp);                                           // guard
                putinar1.addPredicate(v.pre_condition);
                putinar1.addPredicate(qc);                                       // ~ (rank ^ non-neg)
                putinar1.addPredicate(new PolynomialPredicate(v.inv));
                PolynomialPredicate rankLast1 = rank(en.lastElement());
                putinar1.setObjective(rankLast1.exprs.firstElement());               // f(u_n) <= f(v) - 1
                putinarVector.add(putinar1);

                Putinar putinar2 = new Putinar(v.id, en.lastElement().to.id);
                putinar2.addPredicate(lp);
                putinar2.addPredicate(v.pre_condition);
                putinar2.addPredicate(qc);
                putinar2.addPredicate(new PolynomialPredicate(v.inv));
                PolynomialPredicate rankLast2 = nonNegativity(en.lastElement());
                putinar2.setObjective(rankLast2.exprs.firstElement());           // f(u_n) >= 0
                putinarVector.add(putinar2);
            }
        }
    }

    public static PolynomialPredicate rank(Transition tau) //  0 <= f(u) <= f(v) - 1
    {
        if(tau.to.isBuchi)
            return new PolynomialPredicate(new Polynomial(Monomial.one,Rational.one));          //TODO: check heuristic
        Polynomial from = tau.from.rank.deepCopy();
        from.add(new Polynomial(Rational.negate(Rational.one)));     // f(v) - 1

        Polynomial to = tau.to.rank.deepCopy();                 // f(u)
        to.replaceVarsWithPoly(tau.varName, tau.update);
        from.add(to.negate());                                              // f(v) - f(u) - 1
        return new PolynomialPredicate(from);
    }

    public static PolynomialPredicate nonNegativity(Transition tau)
    {
        Polynomial qc = tau.to.rank.deepCopy();
        qc.replaceVarsWithPoly(tau.varName, tau.update);
        return new PolynomialPredicate(qc);
    }

    // processPaths: uses dfs to generate a putinar for every path outgoing from the starting node
    private static void processPaths(CFGNode v, Vector<Transition> path, Vector<Transition> transitionVector)
    {
        Vector<Transition> tran=v.out;

        for(Transition t:tran)
        {
            CFGNode u=t.to;
            path.add(t);


            if(u.isCutPoint)
            {
                Transition tau = CFGUtil.weakestPreCondition(path);
                transitionVector.add(tau);
//                addPutinar(tau, putinarVector);
            }
            else
                processPaths(u,path,transitionVector);
            path.removeElementAt(path.size()-1);
        }
    }



}