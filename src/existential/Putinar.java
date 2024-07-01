import java.util.Set;
import java.util.TreeSet;
import java.util.Vector;

public class Putinar
{
    public static int countD = 0;
    int startDIndex;
    int startNode, endNode;
    //    private PolynomialPredicate nodeConstraint; //TODO: change name: constraints from start node
    private PolynomialPredicate constraints; //TODO: change name: constraints from transition

    private Polynomial objective;

    Putinar(int startNode, int endNode)
    {
        this.startNode = startNode;
        this.endNode = endNode;
        constraints = new PolynomialPredicate();
        Polynomial lc = new Polynomial();
        lc.add(Monomial.one, Rational.one);
        constraints.add(lc); // 1>=0 is always true

//        nodeConstraint = new PolynomialPredicate();

        startDIndex = countD;
        countD++; // for 1>=0
    }

    public PolynomialPredicate getConstraints()
    {
        return constraints;
    }

    public Putinar deepCopy()
    {
        Putinar ret = new Putinar(startNode, endNode);
        countD--; // for 1>=0 which is added in new
        ret.startDIndex = startDIndex;
//        ret.nodeConstraint.exprs.addAll(nodeConstraint.exprs);

        //countD+=invConstraint.size();

        ret.constraints = constraints.deepCopy();
        //countD+=linearConstraints.exprs.size()-1; //-1 for 1>=0 which is already added

        ret.objective = objective.deepCopy();
        return ret;
    }

    void addPredicate(PolynomialPredicate pp)
    {
        constraints.add(pp);
        countD+=pp.exprs.size();
    }


    void setObjective(Polynomial obj)
    {
        objective = obj.deepCopy();
    }

    public void apply_heuristic()
    {
        if(Main.degree == 1)
            return;
        PolynomialPredicate heu = new PolynomialPredicate();
        for(Polynomial poly1: constraints.exprs)
        {
            if(poly1.degree()<=1)
            {
                Polynomial mult = poly1.deepCopy();
                mult.multiplyByPolynomial(poly1);
                heu.add(mult);
            }
        }
        constraints.add(heu);
    }

    public DNFPoly generateEqualities()
    {
        PolynomialPredicate equalities1 = new PolynomialPredicate();  // poly = 0
        PolynomialPredicate equalities2;
        Polynomial right = new Polynomial();
        for(Polynomial poly:constraints.exprs)
        {
            Polynomial h = generateHPolynomial(Parser.allVars,Main.mu);
            Polynomial sos = generateSOSPolynomial(Parser.allVars,Main.mu);

            equalities1.addAll(makeEqualities(h,sos));
            h.multiplyByPolynomial(poly);
            right.add(h);
        }
        equalities2= equalities1.deepCopy();
        equalities1.addAll(makeEqualities(objective,right));

        Polynomial contradiction = new Polynomial(Monomial.one, Rational.negate(Rational.one));
        equalities2.addAll(makeEqualities(contradiction, right));
        DNFPoly ret = new DNFPoly();
        ret.or(equalities1);
//        ret.or(equalities2);
        return ret;
    }

    private Polynomial generateHPolynomial(Set<String> vars,int degree)
    {
        Set<Monomial> monomials= Monomial.getAllMonomials(vars,degree);
        Polynomial h=new Polynomial();
        for(Monomial m:monomials)
        {
            Monomial mp=m.deepCopy();
            mp.addVar("t_"+RankingFunction.tCount,1);
            RankingFunction.tCount++;
            h.add(mp,Rational.one);
        }
//        System.err.println("H Poly: "+ h.toNormalString());
        return h;
    }

    private Polynomial generateSOSPolynomial(Set<String> vars, int degree) // ret = y LL^T y^t
    {
        if(degree==0) //NOTE: if not comment it will be Farkas when mu=0
        {
            String var = "l_"+RankingFunction.lCount;
            RankingFunction.lCount++;
            RankingFunction.nonNegativeLvars.add(var);
            Polynomial sos = new Polynomial(new Monomial(var,1));
            return sos;
        }
        Vector<Monomial> tmp = new Vector<>(Monomial.getAllMonomials(vars,degree/2));

        Vector<Polynomial> y=new Vector<>();
        int dim = tmp.size();
        Polynomial[][] L = new Polynomial[dim][dim],Lt=new Polynomial[dim][dim],yt=new Polynomial[dim][1];

        for(int i=0;i<dim;i++)
        {
            y.add(new Polynomial(tmp.elementAt(i)));
            yt[i][0]=new Polynomial(tmp.elementAt(i));
        }

        for(int i=0;i<dim;i++)
            for (int j=0;j<dim;j++)
            {
                if (j <= i)
                {
                    String var = "l_" + RankingFunction.lCount;
                    RankingFunction.lCount++;
                    L[i][j] = new Polynomial(var);
                    Lt[j][i] = L[i][j].deepCopy();
                    if (i == j)
                        RankingFunction.nonNegativeLvars.add(var);
                }
                else
                {
                    L[i][j] = new Polynomial();
                    Lt[j][i] = L[i][j].deepCopy();
                }
            }

        Vector<Polynomial> yL = mulVecMat(y,L);
        Vector<Polynomial> yLLt = mulVecMat(yL,Lt);
        Polynomial ret= new Polynomial();
        for(int i=0;i<dim;i++)
            ret.add(Polynomial.mul(yLLt.elementAt(i), yt[i][0]));

//        System.err.println("SOS: "+ret.toNormalString());
        return ret;
    }

    private Vector<Polynomial> mulVecMat(Vector<Polynomial> y,Polynomial[][] L)
    {
        Vector<Polynomial> ret= new Vector<>();
        int sz=y.size();
        for(int col=0;col<sz;col++)
        {
            Polynomial p=new Polynomial();
            for(int i=0;i<sz;i++)
                p.add(Polynomial.mul(y.elementAt(i),L[i][col]));
            ret.add(p);
        }
        return ret;
    }

    Vector<Polynomial> makeEqualities(Polynomial left, Polynomial right)  //TODO
    {
        Set<Monomial> allMonomials= new TreeSet<>();
        allMonomials.addAll(left.getProgramVariableMonomials());
        allMonomials.addAll(right.getProgramVariableMonomials());

        Vector<Polynomial> ret=new Vector<>();
        for(Monomial m:allMonomials)
        {
            Polynomial leftm=left.getCoef(m),rightm=right.getCoef(m);
            rightm.add(leftm.negate());
            ret.add(rightm);
        }

        return ret;
    }

    public Set<Monomial> getAllVars()
    {
        Set<Monomial> ret=new TreeSet<>();
        for(Polynomial lc: constraints.exprs)
            ret.addAll(lc.terms.keySet());
//        for(Polynomial qc: nodeConstraint.exprs)
//            ret.addAll(qc.terms.keySet());
        ret.addAll(objective.terms.keySet());
        return ret;
    }

//    public QuadraticCombination makeEquality(String var)
//    {
//        QuadraticCombination qc = new QuadraticCombination();
//        int dIndex = startDIndex;
//        if (!invConstraint.exprs.isEmpty())
//        {
//            //for(int i=0;i<invConstraint.exprs.size();i++)
//            for (QuadraticCombination invc : invConstraint.exprs)
//            {
//                if (invc.coef.containsKey(var))
//                {
//                    String invMultiplier = "d_" + dIndex;
//                    //InvariantGeneration.addUnknownVar("d_" + dIndex);
//
//
//                    LinearCombination lc = invc.coef.get(var);
//                    qc.add(invMultiplier, lc);
//                }
//                dIndex++;
//            }
//        }
//
//        for (LinearCombination lp : linearConstraints.exprs) // lp>=0
//        {
//            String multiplier = "d_" + dIndex;
//            if (lp.coef.containsKey(var))
//            {
//                Rational coef = lp.coef.get(var);
//                qc.add(multiplier, new LinearCombination(coef));
//                //InvariantGeneration.addUnknownVar("d_" + dIndex);
//            }
//            dIndex++;
//        }
//
//        LinearCombination coef = objective.getCoef(var);
//        //qc=coef  <=>  qc-coef=0
//        if (coef != null)
//        {
//            LinearCombination lc = coef.negate();
//            qc.add(lc);
//        }
////        System.err.println("var: "+var+" => "+qc.toNormalString());
//        return qc;
//    }

    public String toString()
    {
        String ret = "";
        ret += "\n---------------------------------------------\n";
        ret += "from: " + startNode + " to: " + endNode + "\n";
        int dIndex = startDIndex;
//        for (int i = 0; i < nodeConstraint.exprs.size(); i++)
//        {
//            ret += "d_" + dIndex + ": " + nodeConstraint.exprs.elementAt(i).toNormalString() + "\n";
//            dIndex++;
//        }
        for (Polynomial lc : constraints.exprs)
        {
            ret += "\nd_" + dIndex + ": " + lc.toNormalString();
            dIndex++;
        }
        ret += "\n---------------------------------------------\n";

        ret += objective.toNormalString();
        return ret;
    }
}