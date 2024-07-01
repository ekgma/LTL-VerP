import java.util.Vector;

public class CFGUtil
{

    public static void remove_unreachable()
    {
        Vector<Transition> to_be_removed = new Vector<>();
        for(int node_id: InvUtil.unreachable)
            for(Transition tau: Transition.allTransitions)
            {
                if(tau.from.id == node_id || tau.to.id == node_id)
                    to_be_removed.add(tau);
            }
        for(Transition tau: to_be_removed)
        {
            Transition.allTransitions.remove(tau);
            tau.from.out.remove(tau);
        }
    }
    public static Vector<Integer> detect_Cutpoints()
    {
        Vector<Integer> ret=new Vector<>();
        ret.add(Main.startNode.id);
        dfs(Main.startNode,ret,new Vector<CFGNode>());
        return ret;
    }

    private static void dfs(CFGNode v,Vector<Integer> res,Vector<CFGNode> currentBranch)
    {
        v.visited=true;
        currentBranch.add(v);
        for(Transition t:v.out)
        {
            if(!t.to.visited)
                dfs(t.to, res, currentBranch);
            else if(!res.contains(t.to.id) && currentBranch.contains(t.to))
                res.add(t.to.id);
        }
        currentBranch.removeElementAt(currentBranch.size()-1);
    }


    public static Transition weakestPreCondition(Vector<Transition> path)  //NOTE: for C-Integer programs this is completely fine but for general T2 transition systems it might have problems
    {
        Transition tau = new Transition(path.elementAt(0).from, path.lastElement().to);
        for(String var: Parser.allVars)
            if(!var.equals("1"))
            {
                tau.varName.add(var);
                tau.update.add(new Polynomial(var));
            }
        for(int i=path.size()-1;i>=0;i--)
        {
            Transition t=path.elementAt(i);
            tau.replaceVarsWithPoly(t.varName, t.update);
            tau.detGuard.add(t.detGuard.deepCopy());
        }
        return tau;
    }
}
