package proofs;

import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableMap;
import node.*;

import java.util.*;

/**
 * Created by Roman on 24/02/2017.
 */
public class PCalculus {

    public static final String IMPL = "->";
    public static final String AND = "&";
    public static final String OR = "|";
    public static final String NOT = "!";
    public static final String FORALL = "@";
    public static final String EXISTS = "?";
    public static final String TERM = "theta";
    // meta variables in axiom schemes
    public static final String VAR = "a";
    public static final String FORMULA = "f";
    public static final String FORMULA_SUBST = "f[a:=theta]";

    public static final Var A = new Var("A");
    public static final Var B = new Var("B");
    public static final Var C = new Var("C");

    public static final Node[] SCHEMES = {
            new Impl(A, new Impl(B, A)),
            new Impl(new Impl(A, B),
                    new Impl(new Impl(A, new Impl(B, C)), new Impl(A, C))),
            new Impl(A, new Impl(B, new And(A, B))),
            new Impl(new And(A, B), A),
            new Impl(new And(A, B), B),
            new Impl(A, new Or(A, B)),
            new Impl(B, new Or(A, B)),
            new Impl(new Impl(A, C), new Impl(new Impl(B, C), new Impl(new Or(A, B), C))),
            new Impl(new Impl(A, B), new Impl(new Impl(A, new Not(B)), new Not(A))),
            new Impl(new Not(new Not(B)), B)
    };

    public static AnnotatedNode applyScheme(int i, ImmutableMap<String, Node> map) {
        return new AnnotatedNode(SCHEMES[i].apply(map), new ProofType.Scheme(i));
    }

    public static AnnotatedNode applyScheme(Node scheme, ImmutableMap<String, Node> map) {
        return new AnnotatedNode(scheme.apply(map), new ProofType.Scheme());
    }

    public static Node MP(Node f, int... times) {
        int t = times.length == 0 ? 1 : times[0];
        final int oldTimes = t;
        System.out.println(f);
        while (f instanceof Impl && t > 0) {
            f = f.getChildren().get(1);
            System.out.println(f);
            --t;
        }
        if (t != 0)
            throw new IllegalArgumentException(
                    "unable to apply MP to formula " + f + " " + oldTimes + " time(s)");
        else return f;
    }

    public static List<Node> listMP(Impl f) {
        return ImmutableList.of(f, f.getRight());
    }

    public static class Scheme extends Impl {
        public Scheme(String type) {
            super(new Quantified(type, VAR, new Var(FORMULA)), new Var(FORMULA_SUBST));
            if (type.equals(EXISTS)) {
                Node tmp = children.get(0);
                children.set(0, children.get(1));
                children.set(1, tmp);
            }
        }

        @Override
        public Node apply(Map<String, Node> applyMap, boolean... p) {
            Node termMapping = applyMap.get(TERM);
            Node res = super.apply(applyMap);
            if (termMapping instanceof Term) {
                res = res.apply(Collections.singletonMap(FORMULA_SUBST,
                        applyMap.get(FORMULA).subst((Var) applyMap.get(VAR), termMapping)
                ));
            }
            if (p.length > 0 && p[0])
                System.out.println(res);
            return res;
        }
    }

    public static Node generalize(Node f, Var x) {
        if (x.equals(Arithmetic.Z))
            return f;
//        assert !x.name.equals(Arithmetic.ZERO);
        Eq eq = new Eq(Arithmetic.Z, Arithmetic.Z);
        Map<String, Node> map = new HashMap<>();
        map.put("A", eq);
        map.put("B", eq);
        Node truth = SCHEMES[0].apply(map);
        map.put("A", f);
        map.put("B", truth);
        // f -> T -> f
        Node n = SCHEMES[0].apply(map);
        // T -> f
        MP(n);
        // T -> @x(f)
        Impl impl = new Impl(truth, new Quantified(FORALL, x.getName(), f));
        System.out.println(impl);
        return MP(impl);
    }

    public static Node generalize(Node f, Set<String> toGen, boolean proveGen) {
        for (String var : toGen) {
            if (!proveGen) {
                try {
                    f = new Quantified(PCalculus.FORALL, var, f);
                } catch (IllegalArgumentException e) {
//                    System.err.println(e.getMessage());
                }
            } else
                f = PCalculus.generalize(f, new Var(var));
        }
        return f;
    }

    public static Node generalize(Node f, boolean proveGen) {
        return generalize(f, f.getVars(), proveGen);
    }

    // f -> g, g -> h
    public static Impl useImplTransitivity(Impl first, Impl second) {
        Node f = first.getLeft();
        Node g = second.getLeft();
        if (!g.equals(first.getRight()))
            throw new IllegalArgumentException("not connected implications " +
                    first + " and\n" + second);
        Node h = second.getRight();
        MP(SCHEMES[0].apply(ImmutableMap.of("A", new Impl(g, h), "B", f)));
        return (Impl) MP(SCHEMES[1].apply(ImmutableMap.of("A", f, "B", g, "C", h)), 2);
    }


    /**
     * given alpha -> beta -> gamma, proves beta -> alpha -> gamma
     */
    public static Impl reverseImpl(Node alpha, Node beta, Node gamma) {
        Node omega = new Impl(alpha, new Impl(beta, gamma));
        Deductions.deduction(omega, Deductions.deduction(beta));
        Node apply = SCHEMES[0].apply(ImmutableMap.of(
                "A", beta, "B", alpha
        ));
        System.out.println(apply);
        // omega -> beta -> alpha -> beta
        Impl antecedent = (Impl) Deductions.deduction(omega, apply).getRight();
        // (alpha->beta->gamma)->(alpha->beta)->(alpha->gamma)
        apply = SCHEMES[1].apply(ImmutableMap.of(
                "A", alpha, "B", beta, "C", gamma
        ));
        System.out.println(apply);
        Impl impl = (Impl) Deductions.deduction(omega, Deductions.deduction(beta, apply)).getRight();
        // omega -> beta -> omega -> alpha -> gamma
        Impl phi2 = Deductions.deduction(omega, Deductions.deduction(beta, antecedent, impl));
        // omega -> beta -> omega
        Impl phi1 = (Impl) SCHEMES[0].apply(ImmutableMap.of(
                "A", omega, "B", beta
        ));
        System.out.println(phi1);
        // omega ->
        apply = SCHEMES[1].apply(ImmutableMap.of(
                "A", beta, "B", omega, "C", new Impl(alpha, gamma)
        ));
        System.out.println(apply);
        Impl phi3 = Deductions.deduction(omega, apply);
        return (Impl) MP(Deductions.deduction(omega, phi2, Deductions.deduction(omega, phi1, phi3)));
    }

    /**
     * @see PCalculus#reverseImpl(Node, Node, Node)
     */
    public static Impl reverseImpl(Impl impl) {
        try {
            Impl rightImpl = (Impl) impl.getRight();
            return reverseImpl(impl.getLeft(), rightImpl.getLeft(), rightImpl.getRight());
        } catch (ClassCastException e) {
            return null;
        }
    }


    public static Node MP(Node first, Impl second) {
        if (second.getLeft().equals(first))
            return second.getRight();
        throw new IllegalArgumentException("invalid MP: " + first + " " + second);
    }

    public static AnnotatedNode annotatedMP(Node first, Impl second) {
        if (second.getLeft().equals(first))
            return new AnnotatedNode(second.getRight(), new ProofType.MP(first));
        throw new IllegalArgumentException("invalid MP: " + first + " " + second);
    }

    public static List<AnnotatedNode> annotatedMP(AnnotatedNode annotatedNode) {
        return annotatedMP(annotatedNode, 1);
    }

    public static List<AnnotatedNode> annotatedMP(AnnotatedNode annotatedNode, int times) {
        List<AnnotatedNode> annotatedNodes = new ArrayList<>();
        Node cur = annotatedNode.node;
        annotatedNodes.add(annotatedNode);
        for (int i = 0; i < times; i++) {
            try {
                Node left = ((Impl) cur).getLeft();
                cur = ((Impl) cur).getRight();
                annotatedNodes.add(new AnnotatedNode(cur, new ProofType.MP(left)));
            } catch (ClassCastException e) {
                throw new IllegalArgumentException("invalid MP: " + cur + " must be an implication");
            }
        }
        return annotatedNodes;
    }

    static List<Node> forall(Impl impl, String var) {
        return ImmutableList.of(impl, new Impl(impl.getLeft(), new Quantified(FORALL, var, impl.getRight())));
    }

    static List<Node> exists(Impl impl, String var) {
        return ImmutableList.of(impl, new Impl(new Quantified(EXISTS, var, impl.getLeft()), impl.getRight()));
    }
}
