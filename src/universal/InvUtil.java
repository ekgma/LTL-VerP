import java.io.BufferedReader;
import java.io.File;
import java.io.FileWriter;
import java.io.InputStreamReader;
import java.util.*;
import java.util.concurrent.TimeUnit;


public class InvUtil
{
    public static Set<Integer> unreachable = new TreeSet<>();
    public static Set<String> zero_tmp_vars = new TreeSet<>();

    public static boolean checkNonTermination(Vector<Putinar> putinarVector, CFGNode startNode) throws Exception
    {
        Vector<DNFPoly> equalities = new Vector<>();
        for(Putinar putinar: putinarVector)
            equalities.add(putinar.generateEqualities());

//        for(int i=0;i<RankingFunction.sCount;i++)
//            zero_tmp_vars.add("s_"+i);
//        for(int i=0;i<RankingFunction.cCount;i++)
//            zero_tmp_vars.add("c_"+i);
//        if(Main.mu !=0 )
//            for(int i=0;i<RankingFunction.tCount;i++)
//                zero_tmp_vars.add("t_"+i);
//        for(int i=0;i<RankingFunction.lCount;i++)
//            zero_tmp_vars.add("l_"+i);

        int round_cnt = 1;
        while(true)
        {
            System.err.println("started round "+round_cnt);
            round_cnt++;
            String Template = "";
            Template += "(set-option :print-success false)\n";
            if(!Main.solver.equals("bclt"))
                Template+="(set-option :produce-unsat-cores true)\n";

            if (Main.solver.equals("bclt"))
            {
                zero_tmp_vars.clear();
                Template += "(set-option :produce-models true)\n" +
                        "(set-option :produce-assertions true)\n" +
                        "(set-logic QF_NIA)\n";
            } else if (Main.solver.equals("mathsat"))
                Template += "(set-option :produce-models true)\n";
            for (int i = 0; i < RankingFunction.cCount; i++)
                Template += "(declare-const c_" + i + " " + Main.varType + " )\n";
            for (int i = 0; i < RankingFunction.sCount; i++)
                Template += "(declare-const s_" + i + " " + Main.varType + " )\n";

            for (int i = 0; i < RankingFunction.lCount; i++)
                Template += "(declare-const l_" + i + " "+Main.varType+")\n";

            for (int i = 0; i < RankingFunction.tCount; i++)
                Template += "(declare-const t_" + i + " "+Main.varType+")\n";


            FileWriter fw = new FileWriter(Main.workingdir + "/" + Main.solver + Main.fileName + ".smt2");
            fw.write(Template);
            int index = 0;
            for (DNFPoly dnf : equalities)
            {
                fw.write("(assert (! " + dnf.toSMT()+  ":named constraint" + index + " ))\n");
                index++;
            }
            for (String lvar : RankingFunction.nonNegativeLvars)
            {
                fw.write("(assert (! (>= " + lvar + " 0) :named constraint" + index + " ))\n");            // lvar>=0
                index++;
            }
            for(String temp_var: zero_tmp_vars)
                fw.write("(assert (! (= 0 "+ temp_var+ ") :named constraint_"+temp_var+" ))\n");

            fw.write("(check-sat)\n");
            fw.write("(get-value (");
            for (int i = 0; i < RankingFunction.cCount; i++)
                fw.write("c_" + i + " ");
            for (int i = 0; i < RankingFunction.sCount; i++)
                fw.write("s_" + i + " ");

            fw.write("))\n");
            fw.write("(get-unsat-core)");
            fw.close();
            Vector<String> core = check();
            if(core.isEmpty())
                return false;
            else if(core.firstElement().equals("True"))
                return true;
            else
                remove_core_temp_vars(core);

        }
    }

    public static void remove_core_temp_vars(Vector<String> core_vars)
    {
        for(String name:core_vars)
            zero_tmp_vars.remove(name);
    }

    public static Vector<String> check() throws Exception
    {
        String[] configs = {"./" + Main.solversDir + "/bclt --file", "./"+Main.solversDir+"/z3 -smt2", "./" + Main.solversDir + "/mathsat"};
        int solverInd = -1;
        if (Main.solver.equals("bclt"))
            solverInd = 0;
        else if (Main.solver.equals("z3"))
            solverInd = 1;
        else if (Main.solver.equals("mathsat"))
            solverInd = 2;
        else if (Main.solver.equals("cvc5"))
            solverInd = 3;
        Process process = Runtime.getRuntime().exec(configs[solverInd] + " " + Main.workingdir + "/" + Main.solver + Main.fileName + ".smt2");
        process.waitFor();
        BufferedReader bufferedReader = new BufferedReader(new InputStreamReader(process.getInputStream()));
        String output = "";
        while (bufferedReader.ready())
        {
            String s = bufferedReader.readLine();
//            System.err.println(s);
            if(s.contains("("))
                output="";
            output += s;
            if (s.equals("sat"))
            {
                System.err.println("SAT!");
                while (bufferedReader.ready())
                    System.err.println(bufferedReader.readLine());
                Vector<String> ret = new Vector<>();
                ret.add("True");
                return ret;
            } else if (s.contains("unknown"))
            {
                System.err.println("SMT solver returned unknown! exiting.");
                System.exit(0);
            }
        }

        return get_vars_from_core(output);
    }

    public static Vector<String> get_vars_from_core(String core)
    {
        Vector<String> ret = new Vector<>();
        core = core.replaceAll("[()]", "");
//        core = core.substring(1,core.length()-1);
        for(String name: core.split("constraint"))
            if(name.startsWith("_"))
                ret.add(name.substring(1).replaceAll("\\s+",""));
        return ret;
    }

    public static boolean get_invariants_aspic() throws Exception
    {
        String ts = make_fst();
        FileWriter fw = new FileWriter(Main.workingdir + "/" + Main.solver + Main.fileName + ".fst");
        fw.write(ts);
        fw.close();
        Map<Integer, PolynomialPredicate> inv = run_aspic();
        if(inv.isEmpty())
            return false;
        add_to_CFG(inv);
        return true;
    }

    public static Map<Integer, PolynomialPredicate> run_aspic() throws Exception
    {
        Map<Integer, PolynomialPredicate> inv = new TreeMap<>();

        Process process = Runtime.getRuntime().exec("./" + Main.solversDir + "/aspicV3.4 -log 0 -cinv " + Main.workingdir + "/" + Main.solver + Main.fileName + ".fst");
        process.waitFor(30, TimeUnit.SECONDS);
        BufferedReader bufferedReader = new BufferedReader(new InputStreamReader(process.getInputStream()));
        Boolean results = false;
        while (bufferedReader.ready())
        {
            String s = bufferedReader.readLine();
            if (s.contains("----->"))
            {
                int node_id = Integer.parseInt(s.substring(1, s.indexOf('-') - 1).replaceAll(" ", ""));

                String bexpr = s.substring(s.lastIndexOf("{"), s.lastIndexOf("}") + 1);
                bexpr = bexpr.replaceAll("\\{0\\}", "-1>=0");
                bexpr = bexpr.replaceAll("\\{", "");
                bexpr = bexpr.replaceAll("\\}", "");


                System.err.println(node_id + " -> " + bexpr);
                if (bexpr.equals("-1>=0"))
                    unreachable.add(node_id);
                Parser.readTokens(bexpr);
                Node tmp = Parser.parseBexpr(null, 0, Parser.getTokenCount() - 1);
                PolynomialPredicate lp = tmp.guard.getClauses().firstElement();
                inv.put(node_id, lp);
            }
        }
        return inv;
    }

    public static void add_to_CFG(Map<Integer, PolynomialPredicate> inv)
    {
        for (CFGNode n : CFGNode.allCFGNodes)
            if (inv.containsKey(n.id))
                n.pre_condition.add(inv.get(n.id));
    }

    public static String make_fst()
    {
        String tmpVar = "";
        String ts = "model input {\nvar ";
        for (String var : Parser.allVars)
            if (!var.equals("1"))
            {
                ts += var + ", ";
                tmpVar = var;
            }
        ts = ts.substring(0, ts.length() - 2) + ";\nstates ";
        for (CFGNode n : CFGNode.allCFGNodes)
            ts += "l" + n.id + ", ";
        ts = ts.substring(0, ts.length() - 2) + ";\n";
        int index = 0;
        for (Transition tau : Transition.allTransitions)
        {
            String tran = "transition t" + index + " := {\n";
            tran += "from := l" + tau.from.id + ";\n";
            tran += "to := l" + tau.to.id + ";\n";
            tran += "guard := ";
            tran += tau.detGuard.toNormalString_linear() + ";\n";
            tran += "action := ";
            if (tau.varName.isEmpty())
                tran += tmpVar + "' = " + tmpVar + ";\n";
            else
            {
                for (int i = 0; i < tau.varName.size(); i++)
                    if(tau.update.elementAt(i).degree()<=1)
                        tran+= tau.varName.elementAt(i) + "' = " + tau.update.elementAt(i).toNormalString() + ",";
                    else
                        tran+= tau.varName.elementAt(i) + "' = ?,";
                tran = tran.substring(0, tran.length() - 1) + ";\n";
            }
            tran += "};\n";
            index++;
            ts += "\n" + tran;
        }
        ts += "}\n\n";
        ts += "strategy s1 {\n" +
                "Region init := {state= l" + Main.startNode.id + " && " + Main.pre_condition.toNormalString_linear() + "};\n" +
                "}";
//        System.err.println(ts);
        return ts;
    }



    public static void get_invariants_sting() throws Exception
    {
        String ts = make_sting();
        FileWriter fw = new FileWriter(Main.workingdir + "/" + Main.solver + Main.fileName + ".sting");
        fw.write(ts);
        fw.close();
        Map<Integer, PolynomialPredicate> inv = run_sting();
        add_to_CFG(inv);
    }

    public static Map<Integer, PolynomialPredicate> run_sting() throws Exception
    {
        Map<Integer, PolynomialPredicate> inv = new TreeMap<>();
        String[] command = {"./" + Main.solversDir + "/lsting", "noch79", "nobhrz03"};
        ProcessBuilder pb = new ProcessBuilder(command).redirectInput(new File(Main.workingdir + "/" + Main.solver + Main.fileName + ".sting"));
        Process process =pb.start();
        process.waitFor(30, TimeUnit.SECONDS);
        BufferedReader bufferedReader = new BufferedReader(new InputStreamReader(process.getInputStream()));
        Boolean read_inv = false;
        int cur_loc_id = -1;
        while (bufferedReader.ready())
        {
            String s = bufferedReader.readLine();
//            System.err.println(s);
            if(read_inv && s.contains("Location:"))
            {
                String[] tmp = s.split(":");
                String loc = tmp[tmp.length-1].substring(1);
                try {
                    cur_loc_id = Integer.parseInt(loc);
                } catch(NumberFormatException e){
                    continue;
                }
            }
            else if(read_inv && s.contains("Invariant: [["))
            {
                while(true)
                {
                    String bexpr = bufferedReader.readLine();
                    if(bexpr.contains("]]"))
                        break;
                    else if(!bexpr.isEmpty())
                    {

                        if (bexpr.contains("false"))
                        {
                            unreachable.add(cur_loc_id);
                            continue;
                        }
                        else if(bexpr.contains("True"))
                            continue;
                        bexpr = bexpr.replace(" = ", " == ");
                        System.err.println(cur_loc_id+" -> "+bexpr);
                        Parser.readTokens(bexpr);
                        Node tmp = Parser.parseBexpr(null, 0, Parser.getTokenCount() - 1);
                        PolynomialPredicate lp = tmp.guard.getClauses().firstElement();
                        if(inv.containsKey(cur_loc_id))
                            inv.get(cur_loc_id).add(lp);
                        else
                            inv.put(cur_loc_id, lp);
                    }
                }
            }
            else if(s.contains("Transition Relation Ends"))
                read_inv = true;

        }
        return inv;
    }
    public static String make_sting()
    {
        StringBuilder ret = new StringBuilder();
        ret.append("variable [");
        for(String var: Parser.allVars)
            if(!var.equals("1"))
                ret.append(var).append(" ");
        ret.append("]\n");
        ret.append("Location ").append("l").append(Main.startNode.id).append("\n");
        for(Polynomial poly: Main.pre_condition.exprs)
            ret.append("\t").append(poly.toNormalString()).append(" >= 0\n");
        ret.append("\n");
        int index = 0;
        for(Transition tau: Transition.allTransitions)
        {
            ret.append("Transition ").append("t").append(index).append(": ").append("l"+tau.from.id).append(", ").append("l"+tau.to.id).append(",\n");
            for(Polynomial poly: tau.detGuard.exprs)
                if(poly.degree()<=1)
                    ret.append("\t").append(poly.toNormalString()).append(" >= 0\n");
            for(int i=0;i<tau.varName.size();i++)
                if(tau.update.elementAt(i).degree()<=1)
                    ret.append("\t'").append(tau.varName.elementAt(i)).append(" = ").append(tau.update.elementAt(i).toNormalString()).append("\n");
                else
                    ret.append("\t'").append(tau.varName.elementAt(i)).append(" = ").append("?").append("\n");
            Vector<String> preserved = new Vector<>();
            for(String var: Parser.allVars)
                if(!tau.varName.contains(var) && !var.equals("1"))
                    preserved.add(var);
            if(!preserved.isEmpty())
            {
                ret.append("\tpreserve[");
                for(int i=0;i<preserved.size();i++)
                {
                    if(i!=0)
                        ret.append(", ");
                    ret.append(preserved.elementAt(i));
                }
                ret.append("]\n");
            }
            ret.append("\n");
            index++;
        }
        ret.append("end");
        return ret.toString();
    }
}