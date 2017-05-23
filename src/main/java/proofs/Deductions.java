package proofs;

import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableMap;
import node.*;

import java.io.FileOutputStream;
import java.io.IOException;
import java.io.PrintStream;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;

/**
 * @author Roman Golchin (romagolchin@gmail.com)
 */
public class Deductions {
    static final Node A = new Var("A");
    static final Node F = new Var("F");
    static final Node P = new Var("P");
    static final List<List<Node>> gammas = ImmutableList.of(
            ImmutableList.of(new Impl(A, new Impl(F, P)), new And(A, F)),
            ImmutableList.of(new Impl(new And(A, F), P), A, F),
            ImmutableList.of(new Impl(A, new Impl(P, F)), P, A)
    );

    public static final List<List<AnnotatedNode>> HELPERS =
            ImmutableList.of(
                    fullDeduction(gammas.get(0), proofWithAssumptions1()),
                    fullDeduction(gammas.get(1), proofWithAssumptions2()),
                    fullDeduction(gammas.get(2), proofWithAssumptions3())
            );
//            Stream.of(
//            fullDeduction(gammas.get(0), proofWithAssumptions1()),
//            fullDeduction(gammas.get(1), proofWithAssumptions2()),
//            fullDeduction(gammas.get(2), proofWithAssumptions3())
//    ).map(l -> l.stream().map(AnnotatedNode::getNode).collect(Collectors.toList()))
//            .collect(Collectors.toList());

    static List<Node> applyPropositionalProof(List<AnnotatedNode> proof, Map<String, Node> map) {
        return proof.stream().map(x -> x.node.apply(map)).collect(Collectors.toList());
    }

    // a -> f -> p, a & f |- p
    static List<AnnotatedNode> proofWithAssumptions1() {
        List<AnnotatedNode> res = new ArrayList<>();
        res.add(AnnotatedNode.assumption(new And(A, F)));
        res.addAll(PCalculus.annotatedMP(PCalculus.applyScheme(3, ImmutableMap.of("B", F))));
        res.addAll(PCalculus.annotatedMP(PCalculus.applyScheme(4, ImmutableMap.of("B", F))));
        res.addAll(PCalculus.annotatedMP(AnnotatedNode.assumption(new Impl(A, new Impl(F, P))), 2));
        return res;
    }

    // a & f -> p, a, f |- p
    static List<AnnotatedNode> proofWithAssumptions2() {
        List<AnnotatedNode> res = new ArrayList<>();
        res.add(AnnotatedNode.assumption(A));
        res.add(AnnotatedNode.assumption(F));
        res.addAll(PCalculus.annotatedMP(PCalculus.applyScheme(2, ImmutableMap.of(
                "A", F, "B", P
        )), 2));
        res.addAll(PCalculus.annotatedMP(AnnotatedNode.assumption(new Impl(new And(A, F), P))));
        return res;
    }


    // a -> p -> f, p, a |- f
    static List<AnnotatedNode> proofWithAssumptions3() {
        List<AnnotatedNode> res = new ArrayList<>();
        List<Node> gamma = gammas.get(2);
        res.add(AnnotatedNode.assumption(gamma.get(1)));
        res.add(AnnotatedNode.assumption(gamma.get(2)));
        res.addAll(PCalculus.annotatedMP(AnnotatedNode.assumption(gamma.get(0)), 2));
        return res;
    }


    public static Impl deduction(Node anything, Node truth) {
        return (Impl) PCalculus.MP(PCalculus.SCHEMES[0].apply(ImmutableMap.of("A", truth, "B", anything)));
    }

    // hypo -> f, hypo -> f -> g, h = f->g
    public static Impl deduction(Node hypo, Impl f, Impl h) {
        if (!hypo.equals(f.getLeft()))
            throw new IllegalArgumentException("f does not contain hypo " + f + " " + hypo);
        else if (!hypo.equals(h.getLeft())) {
            throw new IllegalArgumentException("h doesn't contain hypo " + h + " " + hypo);
        } else if (!f.getRight().equals(((BinaryNode) h.getRight()).getLeft()))
            throw new IllegalArgumentException("f is not antecedent of h " + f + " " + h);
        h = (Impl) h.getRight();
        Node g = h.getRight();
        System.out.println(f);
        System.out.println(new Impl(hypo, h));
        return (Impl) PCalculus.MP(PCalculus.SCHEMES[1].apply(ImmutableMap.of("A", hypo, "B", f.getRight(), "C", g)), 2);
    }

    public static Impl deduction(Node hypo) {
        System.out.println(new Impl(hypo, new Impl(new Impl(hypo, hypo), hypo)));
        System.out.println(new Impl(hypo, new Impl(hypo, hypo)));
        return (Impl) PCalculus.MP(PCalculus.SCHEMES[1].apply(ImmutableMap.of("A", hypo,
                "B", new Impl(hypo, hypo), "C", hypo)), 2);
    }

    /**
     * given alpha -> beta -> gamma1
     * alpha -> beta -> gamma2
     * gamma1 -> gamma2 -> gamma3
     * prove that
     * alpha -> beta -> gamma3
     */
    public static Impl deduction(Node alpha, Node beta, Node gamma1, Node gamma2, Node gamma3) {
        Impl omega = new Impl(gamma1, new Impl(gamma2, gamma3));

        Impl scheme = (Impl) PCalculus.SCHEMES[1].apply((ImmutableMap.of(
                "A", beta, "B", gamma1, "C", new Impl(gamma2, gamma3)
        )));
        System.out.println(scheme);
        // alpha -> beta -> gamma2 -> gamma3
        Impl impl = deduction(alpha,
                // alpha -> beta -> omega
                deduction(alpha, deduction(beta, omega)),
                // alpha -> (beta -> omega) -> beta -> gamma2 -> gamma3
                deduction(alpha, new Impl(alpha, new Impl(beta, gamma1)),
                        // alpha -> (beta -> gamma1) -> (beta -> gamma1 -> gamma2 -> gamma3) -> beta -> gamma2 -> gamma3
                        deduction(alpha, scheme)));

        Node apply = PCalculus.SCHEMES[1].apply((ImmutableMap.of(
                "A", beta, "B", gamma2, "C", gamma3
        )));
        System.out.println(apply);
        scheme = deduction(alpha, apply);

        return deduction(alpha, impl,
                // alpha -> (beta -> gamma2 -> gamma3) -> beta -> gamma3
                deduction(alpha, new Impl(alpha, new Impl(beta, gamma2)), scheme));
    }

    public static List<AnnotatedNode> propositionalDeduction(final Node alpha, AnnotatedNode annotatedNode) {
        Node node = annotatedNode.node;
        ProofType proofType = annotatedNode.type;
        List<AnnotatedNode> res = new ArrayList<>();
        // cases from Propositional Calculus
        if (node.equals(alpha)) {
            res.add(new AnnotatedNode(
                    new Impl(alpha, new Impl(new Impl(alpha, alpha), alpha)), new ProofType.Scheme()));
            res.add(new AnnotatedNode(new Impl(alpha, new Impl(alpha, alpha)), new ProofType.Scheme()));
            res.addAll(PCalculus.annotatedMP(new AnnotatedNode(PCalculus.SCHEMES[1].apply(ImmutableMap.of("A", alpha,
                    "B", new Impl(alpha, alpha), "C", alpha)), new ProofType.Scheme()), 2));
        } else if (proofType instanceof ProofType.Assumption || proofType instanceof ProofType.Scheme) {
            res.add(annotatedNode);
            res.addAll(PCalculus.annotatedMP(PCalculus.applyScheme(0, ImmutableMap.of("A", node, "B", alpha)), 1));
        } else if (proofType instanceof ProofType.MP) {
            ProofType.MP mp = (ProofType.MP) proofType;
            Node phi = mp.first;
            AnnotatedNode scheme = PCalculus.applyScheme(1, ImmutableMap.of("A", alpha, "B", phi, "C", node));
            res.addAll(PCalculus.annotatedMP(scheme, 2));
        }
        return res;
    }

    public static List<Node> deduction(final Node alpha, AnnotatedNode annotatedNode) {
        List<Node> res = propositionalDeduction(alpha, annotatedNode).stream().map(AnnotatedNode::getNode)
                .collect(Collectors.toList());
        if (!res.isEmpty())
            return res;
        Node node = annotatedNode.node;
        ProofType proofType = annotatedNode.type;
        Impl impl = (Impl) node;
        if (proofType instanceof ProofType.Forall) {
            final Quantified right = (Quantified) impl.getRight();
            res.addAll(applyPropositionalProof(HELPERS.get(0),
                    ImmutableMap.of("A", alpha, "F", impl.getLeft(), "P", right.getOperand())
            ));
            Impl afp = (Impl) res.get(res.size() - 1);
            res.addAll(PCalculus.forall((Impl) afp.getRight(), right.getVariable()));
            res.addAll(applyPropositionalProof(HELPERS.get(1),
                    ImmutableMap.of("A", alpha, "F", impl.getLeft(), "P", right))
            );
            res.add(((Impl) res.get(res.size() - 1)).getRight());
        } else if (proofType instanceof ProofType.Exists) {
            Quantified left = (Quantified) impl.getLeft();
            res.addAll(applyPropositionalProof(HELPERS.get(2),
                    ImmutableMap.of("A", alpha, "F", impl.getRight(), "P", left.getOperand()
            )));
            Impl afp = (Impl) res.get(res.size() - 1);
            res.addAll(PCalculus.exists((Impl) afp.getRight(), left.getVariable()));
            res.addAll(applyPropositionalProof(HELPERS.get(2),
                    ImmutableMap.of("A", left, "P", alpha, "F", impl.getRight()))
            );
            res.add(((Impl) res.get(res.size() - 1)).getRight());
        } else throw new IllegalArgumentException();
        return res;
    }


    public static List<AnnotatedNode> fullDeduction(List<Node> gamma, List<AnnotatedNode> proof) {
        return deduction(gamma, proof, gamma.size());
    }

    /**
     * Given annotated proof using assumptions from gamma applies deduction lemma given number of times
     */
    public static List<AnnotatedNode> deduction(List<Node> gamma, List<AnnotatedNode> proof, int times) {
        if (times <= 0)
            return proof;
        List<AnnotatedNode> deduced = new ArrayList<>();
        for (AnnotatedNode annotatedNode : proof) {
            deduced.addAll(propositionalDeduction(gamma.get(gamma.size() - 1), annotatedNode));
        }
        return deduction(gamma.subList(0, gamma.size() - 1), deduced, times - 1);
    }


    public static <T> String lineBreakJoin(List<T> l) {
        return l.stream().map(x -> x.toString()).collect(Collectors.joining("\n", "", "\n"));
    }

    public static void main(String[] args) throws IOException {
        System.out.println(PCalculus.annotatedMP(AnnotatedNode.assumption(new Impl(A, F))));
        System.setOut(new PrintStream(new FileOutputStream("helpers")));
        System.out.println(lineBreakJoin(HELPERS.stream().map(x -> lineBreakJoin(x)).collect(Collectors.toList())));
    }
}
