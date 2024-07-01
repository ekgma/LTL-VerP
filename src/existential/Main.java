import java.util.ServiceConfigurationError;
import java.util.Set;
import java.util.TreeSet;
import java.util.Vector;


public class Main
{
    public static Rational eps = Rational.one;
    public static CFGNode startNode;
    public static String fileName = "", solver = "", workingdir="", solversDir="", varType = "",sting="",aspic="";
    public static Set<Integer> buchi = new TreeSet<>(), Cutpoint = new TreeSet<>();
    public static int degree = 2, mu = 0;
    public static PolynomialPredicate pre_condition = new PolynomialPredicate();
    // test
    public static void main(String[] args) throws Exception
    {
        fileName = args[0];
        solver = args[1];
        workingdir = args[2];
        solversDir = args[3];
        varType = args[4];
        degree = Integer.parseInt(args[5]);
        mu = Integer.parseInt(args[6]);
        sting=args[7];
        aspic=args[8];
//        fileName = "input.t2";
//        workingdir = "work/";
//        solver = "mathsat";
//        solversDir = "solvers/";


        long startTime = System.currentTimeMillis();
        Parser.readFile(fileName);
        Parser.parseProg(0, Parser.getTokenCount() - 1);
        fileName=fileName.replace("/","_");
        Vector<Transition> removed = new Vector<>();
        for(int i=0;i<=pre_condition.exprs.size();i++)
        {
            // ------ set pre-condition -----
            PolynomialPredicate current_pre = null;
            int timeOut = 0;
            if(i<pre_condition.exprs.size())
            {
                Polynomial expr = pre_condition.exprs.elementAt(i);
                current_pre = pre_condition.deepCopy();
                current_pre.add(expr.negate());
                timeOut = 900/pre_condition.exprs.size();
                System.err.println("running with tight pre-condition: "+expr.toNormalString()+" == 0");
            }
            else
            {
                current_pre = pre_condition;
                timeOut = 1800;
            }
            // ------ Init ------
                Cutpoint.clear();
                InvUtil.unreachable.clear();
                for(Transition tau: removed)
                    tau.addToGraph();
                for(CFGNode n: CFGNode.allCFGNodes)
                {
                    n.pre_condition.exprs.clear();
                    n.visited = n.isCutPoint = n.isBuchi = false;
                }
                removed.clear();
            // -------------------
            if(aspic.equals("aspic"))
                InvUtil.get_invariants_aspic(current_pre);
            if (sting.equals("sting"))
                InvUtil.get_invariants_sting(current_pre);
            removed.addAll(CFGUtil.remove_unreachable());
            Cutpoint.addAll(CFGUtil.detect_Cutpoints());
            for (int id : buchi)
                if (!InvUtil.unreachable.contains(id))
                    Cutpoint.add(id);
            for (CFGNode n : CFGNode.allCFGNodes)
            {
                if (Cutpoint.contains(n.id))
                    n.isCutPoint = true;
                if (buchi.contains(n.id))
                    n.isBuchi = true;
            }
            for (CFGNode n : CFGNode.allCFGNodes)
                if (n.isCutPoint)
                    n.addTerminalTransitions();

            RankingFunction.MakeTemplate();
            for (CFGNode n : CFGNode.allCFGNodes)
                if (n.isCutPoint)
                    System.err.println(n.id + ": " + n.rank.toNormalString());
            Vector<Putinar> putinarVector = new Vector<>();
            RankingFunction.generate(putinarVector, current_pre);
            for (Putinar putinar : putinarVector)
                putinar.apply_heuristic();
//            for(Putinar p: putinarVector)
//                System.err.println(p);

            System.err.println(Main.solver + " started");
            boolean result = InvUtil.checkNonTermination(putinarVector, startNode, current_pre, timeOut);
            if (result)
            {
                System.out.println("SAT -> BUCHI proved");
                long endTime = System.currentTimeMillis();
                System.out.println("total time used: " + (endTime - startTime));
                System.exit(3);
            }
            else
                System.err.println("unsat?");
        }
        System.out.println("UNSAT -> Could Not prove BUCHIness");
        System.exit(2);
    }

}