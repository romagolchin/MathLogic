import com.google.common.collect.ImmutableMap;

import java.util.*;

/**
 * Created by Roman on 24/02/2017.
 */
public class PredicateCalculus {

    public static final String IMPL = "->";
    public static final String AND = "&";
    public static final String OR = "|";
    public static final String NEG = "!";
    public static final String FORALL = "@";
    public static final String EXISTS = "?";
    public static final String TERM = "theta";
    // meta variables in axiom schemes
    public static final String VAR = "a";
    public static final String FORMULA = "f";
    public static final String FORMULA_SUBST = "f[a:=theta]";


    public static final Node[] SCHEMES = {
            new Impl(new Var("A"), new Impl(new Var("B"), new Var("A"))),
            new Impl(new Impl(new Var("A"), new Var("B")),
                    new Impl(new Impl(new Var("A"), new Impl(new Var("B"), new Var("C"))),
                            new Impl(new Var("A"), new Var("C")))),
            new Impl(new Var("A"), new Impl(new Var("B"), new Var("A"))),
            new Impl(new Var("A"), new Impl(new Var("B"), new Var("A"))),
            new Impl(new Var("A"), new Impl(new Var("B"), new Var("A"))),
            new Impl(new Var("A"), new Impl(new Var("B"), new Var("A"))),
            new Impl(new Var("A"), new Impl(new Var("B"), new Var("A"))),
            new Impl(new Var("A"), new Impl(new Var("B"), new Var("A"))),
            new Impl(new Var("A"), new Impl(new Var("B"), new Var("A"))),
            new Impl(new Var("A"), new Impl(new Var("B"), new Var("A"))),
            new Scheme(FORALL),
            new Scheme(EXISTS)
    };

    public static Node MP(Node f, int... times) {
        int t = times.length == 0 ? 1 : times[0];
        final int oldTimes = t;
        System.out.println(f);
        while (f instanceof Impl && t > 0) {
            f = f.children.get(1);
            System.out.println(f);
            --t;
        }
        if (t != 0)
            throw new IllegalArgumentException(
                    "unable to apply MP to formula " + f + " " + oldTimes + " time(s)");
        else return f;
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
        if (x.equals(FormalArithmetic.Z))
            return f;
//        assert !x.name.equals(FormalArithmetic.ZERO);
        Eq eq = new Eq(FormalArithmetic.Z, FormalArithmetic.Z);
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
                    f = new Quantified(PredicateCalculus.FORALL, var, f);
                } catch (IllegalArgumentException e) {
                    System.err.println(e.getMessage());
                }
            }
            else
                f = PredicateCalculus.generalize(f, new Var(var));
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

    public static Impl deduction(Node anything, Node truth) {
        return (Impl) MP(SCHEMES[0].apply(ImmutableMap.of("A", truth, "B", anything)));
    }

    // hypo -> f, hypo -> f -> g, h = f->g
    public static Impl deduction(Node hypo, Impl f, Impl h) {
//        System.err.println(f);
//        System.err.println(h);
        if (!hypo.equals(f.getLeft()))
            throw new IllegalArgumentException("f does not contain hypo " + f + " " + hypo);
        else if (!hypo.equals(h.getLeft())) {
            throw new IllegalArgumentException("h doesn't contain hypo " + h + " " + hypo);
        }
        else if (!f.getRight().equals(((BinaryNode) h.getRight()).getLeft()))
            throw new IllegalArgumentException("f is not antecedent of h " + f + " " + h);
        h = (Impl) h.getRight();
        Node g = h.getRight();
        System.out.println(f);
        System.out.println(new Impl(hypo, h));
        return (Impl) MP(SCHEMES[1].apply(ImmutableMap.of("A", hypo, "B", f.getRight(), "C", g)), 2);
    }

    public static Impl deduction(Node hypo) {
        System.out.println(new Impl(new Impl(hypo, new Impl(new Impl(hypo, hypo), hypo))));
        System.out.println(new Impl(hypo, new Impl(hypo, hypo)));
        return (Impl) MP(SCHEMES[1].apply(ImmutableMap.of("A", hypo,
                "B", new Impl(hypo, hypo), "C", hypo)), 2);
    }

}
