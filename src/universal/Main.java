import java.util.Set;
import java.util.TreeSet;
import java.util.Vector;


public class Main
{
    public static Rational eps = Rational.one;
    public static int mu = 2, degree = 0;
    public static CFGNode startNode;
    public static String fileName = "", solver = "", workingdir="", solversDir="", varType="", sting="",aspic="";
    public static Set<Integer> buchi = new TreeSet<>(), Cutpoint = new TreeSet<>();
    public static PolynomialPredicate pre_condition = new PolynomialPredicate();
    // test
    public static void main(String[] args) throws Exception
    {

        fileName = args[0];
        solver = args[1];
        workingdir = args[2];
        solversDir = args[3];
        varType = args[4]; // Real or Int
        degree = Integer.parseInt(args[5]);
        mu = Integer.parseInt(args[6]);
        sting = args[7];
        aspic = args[8];

        long startTime = System.currentTimeMillis();
        Parser.readFile(fileName);
        Parser.parseProg(0, Parser.getTokenCount() - 1);
        fileName = fileName.replace("/", "_");
//        for(Transition tau: Transition.allTransitions)
//            System.err.println(tau.toString());
        if(aspic.equals("aspic"))
            InvUtil.get_invariants_aspic();
        if (sting.equals("sting"))
            InvUtil.get_invariants_sting();
//        System.exit(0);
        CFGUtil.remove_unreachable();
        Cutpoint.clear();       // TODO: remove?
        Cutpoint.addAll(CFGUtil.detect_Cutpoints());
        Cutpoint.addAll(buchi);
        for(CFGNode n: CFGNode.allCFGNodes)
        {
            if(Cutpoint.contains(n.id))
                n.isCutPoint = true;
            if(buchi.contains(n.id))
                n.isBuchi=true;
        }
//
//
        RankingFunction.MakeTemplate();
        for(CFGNode n: CFGNode.allCFGNodes)
            if(n.isCutPoint)
                System.err.println(n.id+": "+n.rank.toNormalString());
        Vector<Putinar> putinarVector = new Vector<>();

        RankingFunction.generate(putinarVector);
        for(Putinar putinar: putinarVector)
            putinar.apply_heuristic();
//        for(Putinar putinar: putinarVector)
//            System.err.println(putinar);
        System.err.println(solver+ " started!");
        boolean result = InvUtil.checkNonTermination(putinarVector, startNode);
        if(result) //does not terminate
            System.out.println("BUCHI proved");
        else
            System.out.println("Could Not prove BUCHIness");

        long endTime = System.currentTimeMillis();
        System.out.println("total time used: " + (endTime - startTime));
        int val = (result) ? 3 : 2;
        System.exit(val);
    }
}