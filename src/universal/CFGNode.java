import java.util.Map;
import java.util.TreeMap;
import java.util.Vector;

public class CFGNode
{
    public static Vector<CFGNode> allCFGNodes = new Vector<>();
    public static Map<Integer, CFGNode> idToNode = new TreeMap<>();
    public static int greatestNodeIndex = 0;


    public Vector<Transition> out;
    int id;
    boolean visited;
    boolean isCutPoint;
    boolean isBuchi;
    public PolynomialPredicate pre_condition;
    Polynomial rank;
    Polynomial inv;
    CFGNode(int ind)
    {
        id = ind;
        idToNode.put(ind, this);
        out = new Vector<>();
        allCFGNodes.add(this);
        visited = isCutPoint = isBuchi =false;
        if (ind > greatestNodeIndex)
            greatestNodeIndex = ind;
        pre_condition = new PolynomialPredicate();
    }

    public static CFGNode addNode(int x)
    {
        if (idToNode.containsKey(x))
            return idToNode.get(x);
        return new CFGNode(x);
    }

}