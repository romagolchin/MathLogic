

import com.google.common.collect.ImmutableMap;

import java.util.*;

//import static PredicateCalculus;

/**
 * Created by Roman on 23/02/2017.
 */
public class FormalArithmetic {
    public static final String EQ = "=";
    public static final String ADD = "+";
    public static final String MUL = "*";
    public static final String INC = "'";
    public static final String ZERO = "0";

    public static final Var A = new Var("a");
    public static final Var B = new Var("b");
    public static final Var C = new Var("c");
    public static final Inc A1 = new Inc(new Var("a"));
    public static final Inc B1 = new Inc(new Var("b"));
    public static final Inc C1 = new Inc(new Var("c"));
    public static final Var Z = new Var(ZERO);

    /**
     * a' + b = (a + b)'
     */
    public static final Eq AXIOM_4_ANALOGUE =
            new Eq(new Add(A1, B), new Inc(new Add(A, B))) {
                @Override
                public void prove() {
                    Node base = subst(B, Z);
//                    System.out.println(AXIOMS[5]);
                    BinaryNode first = applySymmetry(
                            (Eq) PredicateCalculus.MP(AXIOMS[0].rename(ImmutableMap.of("a", new Add(A, Z), "b", A))));
//                    System.out.println("first " + first);
                    AXIOMS[5].apply(ImmutableMap.of("a", A1), true);
                    BinaryNode second = (BinaryNode) PredicateCalculus.MP(
                            SYMMETRY.apply(ImmutableMap.of("x", new Add(A1, Z), "y", A1), true));
//                    System.out.println("second " + second);
                    BinaryNode baseRes = (BinaryNode) PredicateCalculus.MP(
                            AXIOMS[1].rename(ImmutableMap.of("a", first.getLeft(),
                                    "b", first.getRight(), "c", second.getRight())), 2);
                    PredicateCalculus.MP(
                            SYMMETRY.apply(ImmutableMap.of("x", baseRes.getLeft(), "y", baseRes.getRight()), true));

                    Impl step = new Impl(this, subst(B, B1));
//                    System.out.println("STEP " + step);
                    Impl reverseAssumption = (Impl) SYMMETRY.rename(ImmutableMap.of("x", getLeft(), "y", getRight()));
                    PredicateCalculus.deduction(this, AXIOMS[4].rename(ImmutableMap.of("a", A1, "b", B)));
                    applySymmetry((Eq) AXIOMS[4]);
                    // (a + b)' = a' + b -> a + b' = a' + b
                    Impl im = (Impl) PredicateCalculus.MP(AXIOMS[1].rename(ImmutableMap.of("a", new Inc(new Add(A, B)),
                            "b", new Add(A, B1),
                            "c", new Add(A1, B)

                    )));
                    im = PredicateCalculus.useImplTransitivity(reverseAssumption, im);
                    Node node = PredicateCalculus.deduction(this, AXIOMS[0].rename(ImmutableMap.of("a", new Add(A, B1),
                            "b", new Add(A1, B))));
                    node = PredicateCalculus.deduction(this, im, (Impl) node);
                    first = PredicateCalculus.deduction(this, AXIOMS[4].rename(ImmutableMap.of("a", A1, "b", B)));
                    second = PredicateCalculus.deduction(this, (Impl) node,
                            PredicateCalculus.deduction(this, SYMMETRY.rename(ImmutableMap.of(
                                    "x", new Inc(new Add(A, B1)), "y", new Inc(new Add(A1, B))
                            ))));
                    Impl deduction = PredicateCalculus.deduction(this, TRANSITIVITY.apply(ImmutableMap.of(
                            "x", new Add(A1, B1), "y", new Inc(new Add(A1, B)), "z", new Inc(new Add(A, B1))), true));
                    PredicateCalculus.deduction(this, (Impl) second,
                            PredicateCalculus.deduction(this, (Impl) first, deduction));
                    induction(base, step, this, B);
                    super.prove();
                }
            };

    public static final Eq ADD_COMMUTATIVITY =
            new Eq(new Add(A, B),
                    new Add(B, A)) {
                @Override
                public void prove() {
                    //BASE: a + 0 = 0 + a
                    // prove that 0 + a = a
                    Node base = new Eq(new Add(Z, A), A);
                    // 0 + 0 = 0
                    Node baseOfBase = base.subst(A, Z);
//                    AXIOMS[5].apply(ImmutableMap.of("a", Z), true);
                    // FIXME: 02/03/2017 why does commented code fail?
                    AXIOMS[5].rename(ImmutableMap.of("a", Z));
                    Impl stepOfBase = new Impl(base, base.subst(A, A1));
                    Eq eq = new Eq(new Add(Z, A), A);
                    Impl phi = PredicateCalculus.deduction(eq, AXIOMS[4].rename(
                            ImmutableMap.of("a", Z, "b", A)
                    ));
                    Impl psy = (Impl) AXIOMS[0].rename(ImmutableMap.of(
                            "a", new Add(Z, A), "b", A));
                    // 0 + a = a -> 0 + a' = a'
                    PredicateCalculus.deduction(eq, psy,
                            PredicateCalculus.deduction(eq, phi,
                                    PredicateCalculus.deduction(
                                            eq, TRANSITIVITY.rename(ImmutableMap.of(
                                                    "x", new Add(Z, A1),
                                                    "y", new Inc(new Add(Z, A)),
                                                    "z", A1)))));

                    induction(baseOfBase, stepOfBase, base, A);
                    base = applySymmetry(applyTransitivity(eq, ((Eq) AXIOMS[5]).reverse()));
                    //STEP
                    // a + b = b + a -> a + b' = b' + a
                    Node step = new Impl(this, subst(B, B1));
                    // a + b = b + a -> a + b' = (a + b)'
                    Impl first = PredicateCalculus.deduction(this, AXIOMS[4]);
                    // a + b = b + a -> (a + b)' = (b + a)'
                    Impl second = (Impl)
                            AXIOMS[0].rename(ImmutableMap.of("a", new Add(A, B), "b", new Add(B, A)));
                    Impl node = PredicateCalculus.deduction(this, TRANSITIVITY.rename(ImmutableMap.of("x", new Add(A, B1),
                            "y", new Inc(new Add(A, B)), "z", new Inc(new Add(B, A)))));
                    // a + b = b + a -> a + b' = (b + a)'
                    Impl impl = PredicateCalculus.deduction(this, second,
                            PredicateCalculus.deduction(this, first, node));
//                    System.out.println("node = " + node);
                    // this -> b' + a = (b + a)'
                    first = PredicateCalculus.deduction(this, AXIOM_4_ANALOGUE.rename(ImmutableMap.of("a", B, "b", A)));
                    // this -> (b + a)' = b' + a
                    second = PredicateCalculus.useImplTransitivity(first, (Impl) SYMMETRY.rename(ImmutableMap.of(
                            "x", new Add(B1, A),
                            "y", new Inc(new Add(B, A))
                    )));
                    node = PredicateCalculus.deduction(this,
                            TRANSITIVITY.rename(ImmutableMap.of("x", new Add(A, B1),
                                    "y", new Inc(new Add(B, A)), "z", new Add(B1, A))));
//                    System.out.println("node = " + node);
                    PredicateCalculus.deduction(this, second,
                            PredicateCalculus.deduction(this, impl, node));
//                    PredicateCalculus.useImplTransitivity()
//                    PredicateCalculus.deduction(this, PredicateCalculus.deduction());
                    induction(base, step, this, B);
                    super.prove();
                }
            };


    /**
     * b = c -> a * b = a * c
     */
    public static final Impl MUL_SUBST_LEMMA =
            new Impl(new Eq(B, C), new Eq(new Mul(A, B), new Mul(A, C)));


    /**
     * b = c -> a + b = a + c
     */
    public static final Impl ADD_SUBST_LEMMA =
            new Impl(new Eq(B, C), new Eq(new Add(A, B), new Add(A, C))) {
                @Override
                public void prove() {
                    System.out.println(AXIOMS[5].apply(ImmutableMap.of("a", B), true));
                    System.out.println(AXIOMS[5].apply(ImmutableMap.of("a", C), true));
                    // b = c -> 0 + b = 0 + c
                    Node base = subst(A, Z);
                    Map<String, Node> appMap = new HashMap<>();
                    appMap.put("a", Z);
                    appMap.put("b", B);
                    BinaryNode appliedComm = (BinaryNode) ADD_COMMUTATIVITY.rename(appMap);
                    appMap.clear();
                    appMap.put("a", B);
                    BinaryNode addZero = (BinaryNode) AXIOMS[5].apply(appMap);
                    appMap.clear();
                    appMap.put("x", appliedComm.getLeft());
                    appMap.put("y", appliedComm.getRight());
                    appMap.put("z", addZero.getRight());
                    // 0 + b = b
                    BinaryNode appliedTransB = (BinaryNode) PredicateCalculus.MP(TRANSITIVITY.apply(appMap, true), 2);
                    appMap.clear();


                    appMap.put("a", Z);
                    appMap.put("b", C);
                    appliedComm = (BinaryNode) ADD_COMMUTATIVITY.rename(appMap);
                    appMap.clear();
                    appMap.put("a", C);
                    addZero = (BinaryNode) AXIOMS[5].apply(appMap);
                    appMap.clear();
                    appMap.put("x", appliedComm.getLeft());
                    appMap.put("y", appliedComm.getRight());
                    appMap.put("z", addZero.getRight());
                    // 0 + c = c
                    BinaryNode appliedTransC = (BinaryNode) PredicateCalculus.MP(TRANSITIVITY.apply(appMap, true), 2);
                    appMap.clear();
                    appMap.put("x", appliedTransC.getLeft());
                    appMap.put("y", appliedTransC.getRight());
                    // c = 0 + c
                    BinaryNode appliedSym = (BinaryNode) PredicateCalculus.MP(SYMMETRY.rename(appMap));
                    appMap.clear();
                    // b = c -> c = 0 + c
                    PredicateCalculus.MP(PredicateCalculus.SCHEMES[0].apply(ImmutableMap.of(
                            "A", appliedSym, "B", getLeft())));
                    appMap.clear();
                    appMap.put("x", appliedTransB.getLeft());
                    appMap.put("y", appliedTransB.getRight());
                    appMap.put("z", ((BinaryNode) getLeft()).getRight());
                    // b = c -> 0 + b = c
                    BinaryNode bn = (BinaryNode) PredicateCalculus.MP(TRANSITIVITY.apply(appMap, true));
                    appMap.put("x", ((BinaryNode) bn.getRight()).getLeft());
                    appMap.put("y", appliedSym.getLeft());
                    appMap.put("z", appliedSym.getRight());
                    // 0 + b = c -> (c = 0 + c -> 0 + b = 0 + c)
                    bn = (BinaryNode) TRANSITIVITY.apply(appMap, true);
                    appMap.put("A", bn);
                    appMap.put("B", getLeft());
                    // b = c -> 0 + b = c -> (c = 0 + c -> 0 + b = 0 + c)
                    bn = (BinaryNode) PredicateCalculus.MP(PredicateCalculus.SCHEMES[0].apply(appMap));
                    appMap.put("A", getLeft());
                    appMap.put("B", ((BinaryNode) bn.getRight()).getLeft());
                    appMap.put("C", ((BinaryNode) bn.getRight()).getRight());
                    // b = c -> c = 0 + c -> 0 + b = 0 + c
                    PredicateCalculus.MP(PredicateCalculus.SCHEMES[1].apply(appMap), 2);
                    appMap.put("A", getLeft());
                    appMap.put("B", new Eq(C, new Add(Z, C)));
                    appMap.put("C", new Eq(new Add(Z, B), new Add(Z, C)));
                    // b = c -> 0 + b = 0 + c
                    PredicateCalculus.MP(PredicateCalculus.SCHEMES[1].apply(appMap), 2);

                    Impl step = new Impl(this, subst(A, new Inc(A)));
//                    System.out.println("\n\nSTEP = " + step);
                    // b=c->a+b=a+c
                    Impl cur = (Impl) step.getLeft();

                    cur = PredicateCalculus.useImplTransitivity(
                            cur, (Impl) AXIOMS[0].rename(ImmutableMap.of("a", new Add(A, B), "b", new Add(A, C))));
                    System.out.println("CUR = " + cur);


                    Eq hypo = new Eq(new Add(A, new Inc(B)), new Add(A, new Inc(C)));
                    List<Node> eqs = new ArrayList<>();
                    System.out.println(ADD_COMMUTATIVITY);
                    eqs.add(PredicateCalculus.MP(AXIOMS[0].rename(ImmutableMap.of("a", new Add(A, B), "b", new Add(B, A)))));
                    BinaryNode binaryNode = (BinaryNode) AXIOMS[4].rename(ImmutableMap.of("a", B, "b", A));
                    eqs.add(PredicateCalculus.MP(
                            SYMMETRY.apply(ImmutableMap.of("x", binaryNode.getLeft(), "y", binaryNode.getRight()))));
                    eqs.add(ADD_COMMUTATIVITY.rename(ImmutableMap.of("a", B, "b", new Inc(A))));
                    System.out.println("\n\nEQUATIONS B");
                    Eq curEq = (Eq) eqs.get(0);
                    for (int i = 1; i < eqs.size(); i++) {
                        Eq n = (Eq) eqs.get(i);
                        curEq = (Eq) PredicateCalculus.MP(TRANSITIVITY.apply(ImmutableMap.of(
                                "x", curEq.getLeft(), "y", curEq.getRight(), "z", n.getRight()), true), 2);
                    }
                    System.out.println("SUBST TO C");
                    curEq.apply(ImmutableMap.of("b", C), true, true);
                    Impl impl = (Impl) PredicateCalculus.MP(AXIOMS[1].rename(ImmutableMap.of("a", curEq.getLeft(),
                            "b", curEq.getRight(),
                            "c", hypo.getRight())));
                    PredicateCalculus.deduction(hypo,
                            new Eq(new Inc(new Add(A, C)), new Add(A1, C)));
                    Node phi = impl.getLeft();
                    Node psy1 = impl.getRight();
                    Node psy2 = new Eq(new Inc(new Add(A, C)), new Add(A1, C));
                    Node psy3 = TRANSITIVITY.rename(ImmutableMap.of("x", new Add(A1, B), "y", new Inc(new Add(A, C)),
                            "z", new Add(A1, C)));
                    PredicateCalculus.MP(PredicateCalculus.SCHEMES[1].apply(ImmutableMap.of("A", phi, "B", psy1, "C", new Impl(psy2, psy3))), 2);
                    PredicateCalculus.MP(PredicateCalculus.SCHEMES[1].apply(ImmutableMap.of("A", phi, "B", psy2, "C", psy3)), 2);

                    induction(base, step, this, A);
                    super.prove();
                }
            };


    public static final Eq REFLEXIVITY =
            new Eq(new Var("x"), new Var("x")) {
                @Override
                public void prove() {
                    Map<String, Node> map = new HashMap<>();
                    map.put("a", new Add(getLeft(), Z));
                    map.put("b", getLeft());
                    map.put("c", getLeft());
                    AXIOMS[5].apply(ImmutableMap.of("a", new Var("x")), true);
                    PredicateCalculus.MP(AXIOMS[1].apply(map, true), 2);
                    super.prove();
                }
            };

    public static final Impl SYMMETRY =
            new Impl(new Eq(new Var("x"), new Var("y")),
                    new Eq(new Var("y"), new Var("x"))) {
                @Override
                public void prove() {
                    Map<String, Node> map = new HashMap<>();
                    map.put("a", new Var("x"));
                    map.put("b", new Var("y"));
                    map.put("c", new Var("z"));
                    Node pre = AXIOMS[1].apply(map, true);
                    map.clear();
                    map.put("z", new Var("x"));
                    pre.apply(map, true, true);
                    Eq sourceEq = new Eq(new Var("x"), new Var("y"));
                    Eq trueEq = new Eq(new Var("x"), new Var("x"));
                    PredicateCalculus.MP(new Impl(trueEq, new Impl(sourceEq, trueEq)));
                    map.clear();
                    map.put("A", sourceEq);
                    map.put("B", trueEq);
                    map.put("C", sourceEq.reverse());
                    Impl tautology = (Impl) PredicateCalculus.SCHEMES[1].apply(map);
                    PredicateCalculus.MP(tautology, 2);
                    super.prove();
                }
            };

    public static final Impl TRANSITIVITY =
            new Impl(new Eq(new Var("x"), new Var("y")),
                    new Impl(new Eq(new Var("y"), new Var("z")),
                            new Eq(new Var("x"), new Var("z")))) {
                @Override
                public void prove() {
                    Eq revEq = ((Eq) getLeft()).reverse();
                    PredicateCalculus.deduction(getLeft(),
                            AXIOMS[1].apply(ImmutableMap.of(
                                    "a", new Var("y"), "b", new Var("x"), "c", new Var("z")), true));
                    Map<String, Node> map = new HashMap<>();
                    map.put("A", getLeft());
                    map.put("B", revEq);
                    map.put("C", getRight());
                    Impl tautology = (Impl) PredicateCalculus.SCHEMES[1].apply(map);
                    PredicateCalculus.MP(tautology, 2);
                    super.prove();
                }
            };

    /**
     * 0: a = b -> a' = b'
     * 1: a = b -> a = c -> b = c
     * 2: a' = b' -> a = b
     * 3: ! a' = 0
     * 4: a + b' = (a + b)'
     * 5: a + 0 = a
     * 6: a * 0 = 0
     * 7: a * b' = a * b + a
     */
    public static Node[] AXIOMS = {
            new Impl(new Eq(A, B), new Eq(new Inc(A), new Inc(B))),
            new Impl(new Eq(A, B), new Impl(new Eq(A, C), new Eq(B, C))),
            new Impl(new Eq(new Inc(A), new Inc(B)), new Eq(A, B)),
            new Neg(new Eq(new Inc(A), Z)),
            new Eq(new Add(A, new Inc(B)), new Inc(new Add(A, B))),
            new Eq(new Add(A, Z), A),
            new Eq(new Mul(A, Z), Z),
            new Eq(new Mul(A, new Inc(B)), new Add(new Mul(A, B), A))
    };


    /**
     * we assume that base and step of induction are already proven
     *
     * @param f - formula to prove
     * @param x - induction variable
     */


    public static void induction(Node base, Node step, Node f, Var x) {
        Node genStep = PredicateCalculus.generalize(step, x);
//        PredicateCalculus.MP(new Impl(step, genStep));
        PredicateCalculus.MP(new Impl(base, new Impl(genStep, new And(base, genStep))), 2);
        PredicateCalculus.MP(new Impl(new And(base, genStep), f));
    }

    static Eq applySymmetry(Eq eq) {
        return (Eq) PredicateCalculus.MP(
                SYMMETRY.apply(ImmutableMap.of("x", eq.getLeft(), "y", eq.getRight()), true));
    }

    static Eq applyTransitivity(Eq first, Eq second) {
        return (Eq) PredicateCalculus.MP(TRANSITIVITY.rename(ImmutableMap.of("x", first.getLeft(),
                "y", first.getRight(), "z", second.getRight())), 2);
    }


}
