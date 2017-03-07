

import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableMap;
import com.google.common.collect.Lists;

import java.util.*;

//import static PCalculus;

/**
 * Created by Roman on 23/02/2017.
 */
public class Arithmetic {
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
                            (Eq) PCalculus.MP(AXIOMS[0].rename(ImmutableMap.of("a", new Add(A, Z), "b", A))));
//                    System.out.println("first " + first);
                    AXIOMS[5].apply(ImmutableMap.of("a", A1), true);
                    BinaryNode second = (BinaryNode) PCalculus.MP(
                            SYMMETRY.apply(ImmutableMap.of("x", new Add(A1, Z), "y", A1), true));
//                    System.out.println("second " + second);
                    BinaryNode baseRes = (BinaryNode) PCalculus.MP(
                            AXIOMS[1].rename(ImmutableMap.of("a", first.getLeft(),
                                    "b", first.getRight(), "c", second.getRight())), 2);
                    PCalculus.MP(
                            SYMMETRY.apply(ImmutableMap.of("x", baseRes.getLeft(), "y", baseRes.getRight()), true));

                    Impl step = new Impl(this, subst(B, B1));
//                    System.out.println("STEP " + step);
                    Impl reverseAssumption = (Impl) SYMMETRY.rename(ImmutableMap.of("x", getLeft(), "y", getRight()));
                    PCalculus.deduction(this, AXIOMS[4].rename(ImmutableMap.of("a", A1, "b", B)));
                    // (a + b)' = a + b'
                    applySymmetry((Eq) AXIOMS[4]);
                    // (a + b)' = a' + b -> a + b' = a' + b
                    Impl im = (Impl) PCalculus.MP(AXIOMS[1].rename(ImmutableMap.of("a", new Inc(new Add(A, B)),
                            "b", new Add(A, B1),
                            "c", new Add(A1, B)

                    )));
                    im = PCalculus.useImplTransitivity(reverseAssumption, im);
                    Node node = PCalculus.deduction(this, AXIOMS[0].rename(ImmutableMap.of("a", new Add(A, B1),
                            "b", new Add(A1, B))));
                    node = PCalculus.deduction(this, im, (Impl) node);
                    first = PCalculus.deduction(this, AXIOMS[4].rename(ImmutableMap.of("a", A1, "b", B)));
                    second = PCalculus.deduction(this, (Impl) node,
                            PCalculus.deduction(this, SYMMETRY.rename(ImmutableMap.of(
                                    "x", new Inc(new Add(A, B1)), "y", new Inc(new Add(A1, B))
                            ))));
                    Impl deduction = PCalculus.deduction(this, TRANSITIVITY.apply(ImmutableMap.of(
                            "x", new Add(A1, B1), "y", new Inc(new Add(A1, B)), "z", new Inc(new Add(A, B1))), true));
                    PCalculus.deduction(this, (Impl) second,
                            PCalculus.deduction(this, (Impl) first, deduction));
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
                    AXIOMS[5].rename(ImmutableMap.of("a", Z));
                    Impl stepOfBase = new Impl(base, base.subst(A, A1));
                    Eq eq = new Eq(new Add(Z, A), A);
                    Impl phi = PCalculus.deduction(eq, AXIOMS[4].rename(
                            ImmutableMap.of("a", Z, "b", A)
                    ));
                    Impl psy = (Impl) AXIOMS[0].rename(ImmutableMap.of(
                            "a", new Add(Z, A), "b", A));
                    // 0 + a = a -> 0 + a' = a'
                    PCalculus.deduction(eq, psy,
                            PCalculus.deduction(eq, phi,
                                    PCalculus.deduction(
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
                    Impl first = PCalculus.deduction(this, AXIOMS[4]);
                    // a + b = b + a -> (a + b)' = (b + a)'
                    Impl second = (Impl)
                            AXIOMS[0].rename(ImmutableMap.of("a", new Add(A, B), "b", new Add(B, A)));
                    Impl node = PCalculus.deduction(this, TRANSITIVITY.rename(ImmutableMap.of("x", new Add(A, B1),
                            "y", new Inc(new Add(A, B)), "z", new Inc(new Add(B, A)))));
                    // a + b = b + a -> a + b' = (b + a)'
                    Impl impl = PCalculus.deduction(this, second,
                            PCalculus.deduction(this, first, node));
//                    System.out.println("node = " + node);
                    // this -> b' + a = (b + a)'
                    first = PCalculus.deduction(this, AXIOM_4_ANALOGUE.rename(ImmutableMap.of("a", B, "b", A)));
                    // this -> (b + a)' = b' + a
                    second = PCalculus.useImplTransitivity(first, (Impl) SYMMETRY.rename(ImmutableMap.of(
                            "x", new Add(B1, A),
                            "y", new Inc(new Add(B, A))
                    )));
                    node = PCalculus.deduction(this,
                            TRANSITIVITY.rename(ImmutableMap.of("x", new Add(A, B1),
                                    "y", new Inc(new Add(B, A)), "z", new Add(B1, A))));
                    PCalculus.deduction(this, second,
                            PCalculus.deduction(this, impl, node));

                    induction(base, step, this, B);
                    super.prove();
                }
            };

    public static final Eq ADD_ASSOCIATIVITY =
            new Eq(new Add(new Add(A, B), C), new Add(A, new Add(B, C))) {
                @Override
                public void prove() {
                    // BASE: a + b + 0 = a + (b + 0)
                    // a + b = a + b + 0 -> a + b = a + (b + 0) -> base
                    ((Eq) AXIOMS[5]).reverse().rename(ImmutableMap.of("a", new Add(A, B)));
                    // b = b + 0
                    ((Eq) AXIOMS[5]).reverse().rename(ImmutableMap.of("a", B));
                    PCalculus.MP(ADD_SUBST_LEMMA.rename(ImmutableMap.of("a", A, "b", B, "c", new Add(B, Z))));
                    // a + b = (a + b) + 0 -> a + b = a + (b + 0) -> (a + b) + 0 = a + (b + 0)
                    PCalculus.MP(AXIOMS[1].rename(ImmutableMap.of("a", new Add(A, B),
                            "b", new Add(new Add(A, B), Z), "c", new Add(A, new Add(B, Z)))), 2);
                    // STEP
                    // this -> a + b + c' = a + (b + c')
                    // this -> (b + c') = (b + c)'
                    Impl antecedent = PCalculus.deduction(this, AXIOMS[4].rename(ImmutableMap.of("a", B, "b", C)));
                    // this -> a + (b + c') = a + (b + c)'
                    Impl transLeft = PCalculus.deduction(this, antecedent,
                            PCalculus.deduction(this, ADD_SUBST_LEMMA.rename(ImmutableMap.of(
                                    "a", A, "b", ((BinaryNode) antecedent.getRight()).getLeft(),
                                    "c", ((BinaryNode) antecedent.getRight()).getRight()
                            ))));
                    // ... = (a + (b + c))'
                    Impl transRight = PCalculus.deduction(this, AXIOMS[4].rename(ImmutableMap.of(
                            "a", A, "b", new Add(B, C)
                    )));
                    List<Eq> transList = Lists.newArrayList((Eq) transLeft.getRight(), (Eq) transRight.getRight());
//                    System.out.println(transList);
                    System.err.println("transList " + transList.get(0) + " " + transList.get(1));
                    // this -> a + (b + c') = (a + (b + c))'
                    Eq res = processEqChain(this, transList);
                    transList.clear();
                    // this -> a + b + c' = (a + b + c)'
                    transList.add((Eq) PCalculus.deduction(this,
                            AXIOMS[4].rename(ImmutableMap.of("a", new Add(A, B), "b", C))).getRight());
                    transList.add((Eq) ((BinaryNode)
                            AXIOMS[0].rename(ImmutableMap.of("a", getLeft(), "b", getRight()))).getRight());
                    transList.add((Eq) PCalculus.useImplTransitivity(new Impl(this, res),
                            (Impl) SYMMETRY.rename(ImmutableMap.of(
                                    "x", getRight().subst(C, C1), "y", new Inc(getRight())))).getRight());
                    System.err.println(processEqChain(this, transList));
                    induction(subst(C, Z), new Impl(this, subst(C, C1)), this, C);
                    super.prove();
                }
            };

    /**
     * a' * b = a * b + b
     */
    public static final Eq AXIOM_7_ANALOGUE =
            new Eq(new Mul(A1, B), new Add(new Mul(A, B), B)) {
                @Override
                public void prove() {
                    // a' * 0 = a * 0 + 0
                    Node base = subst(B, Z);
                    // a' * 0 = 0
                    AXIOMS[6].rename(ImmutableMap.of("a", A1));
                    List<Eq> baseEqs = new ArrayList<>();
                    baseEqs.add((Eq) ADD_COMMUTATIVITY.rename(ImmutableMap.of("a", new Mul(A, Z),
                            "b", Z)));
                    baseEqs.add((Eq) PCalculus.MP(ADD_SUBST_LEMMA.rename(ImmutableMap.of(
                            "a", Z, "b", new Mul(A, Z), "c", Z
                    ))));
                    baseEqs.add((Eq) AXIOMS[5].rename(ImmutableMap.of("a", Z)));
                    Eq baseEq = null;
                    for (int i = 0; i < baseEqs.size() - 1; i++) {
                        baseEq = applyTransitivity(new Eq(baseEqs.get(0).getLeft(), baseEqs.get(i).getRight()),
                                baseEqs.get(i + 1));
                    }
                    System.err.println(baseEq);
                    applyTransitivity((Eq) AXIOMS[6].rename(ImmutableMap.of("a", A1)), applySymmetry(baseEq));
                    Impl step = new Impl(this, subst(B, B1));
                    Eq assumption = new Eq(new Mul(A1, B), new Add(new Mul(A, B), B));
                    // chain of equations proving that a' * b = a * b + b ->
                    // a' * b + a = a * b + (a + b)
                    List<Impl> impls = new ArrayList<>();
                    List<Eq> eqs = new ArrayList<>();
                    // a' * b + a = a + a' * b
                    impls.add(PCalculus.deduction(assumption,
                            ADD_COMMUTATIVITY.rename(ImmutableMap.of(
                                    "a", new Mul(A1, B), "b", A
                            ))));
                    // = a + (ab + b)
                    impls.add((Impl) ADD_SUBST_LEMMA.rename(ImmutableMap.of(
                            "a", A, "b", new Mul(A1, B), "c", new Add(new Mul(A, B), B)
                    )));
                    // = ab + b + a
                    impls.add(PCalculus.deduction(assumption,
                            ADD_COMMUTATIVITY.rename(ImmutableMap.of(
                                    "a", A, "b", new Add(new Mul(A, B), B)
                            ))));
                    // = ab + (b + a)
                    impls.add(PCalculus.deduction(assumption,
                            ADD_ASSOCIATIVITY.rename(ImmutableMap.of(
                                    "a", new Mul(A, B), "b", B, "c", A
                            ))));
                    // = ab + (a + b)
                    applySymmetry(ADD_COMMUTATIVITY);
                    Eq eq = (Eq) PCalculus.MP(ADD_SUBST_LEMMA.rename(ImmutableMap.of(
                            "a", new Mul(A, B), "b", new Add(B, A), "c", new Add(A, B)
                    )));
                    impls.add(PCalculus.deduction(assumption, eq));
                    // = ab + a + b
                    impls.add(PCalculus.deduction(assumption,
                            applySymmetry((Eq) ADD_ASSOCIATIVITY.rename(ImmutableMap.of(
                                    "a", new Mul(A, B), "b", A, "c", B
                            )))));
                    // = b + (ab + a)
                    impls.add(PCalculus.deduction(assumption,
                            ADD_COMMUTATIVITY.rename(ImmutableMap.of(
                                    "a", new Add(new Mul(A, B), A), "b", B
                            ))));
                    // = b + ab'
                    impls.add(PCalculus.useImplTransitivity(PCalculus.deduction(assumption,
                            ((Eq) AXIOMS[7]).reverse()), (Impl)
                            ADD_SUBST_LEMMA.rename(ImmutableMap.of("a", B, "b", new Add(new Mul(A, B), A),
                                    "c", new Mul(A, B1)))));
                    // = ab' + b
                    impls.add(PCalculus.deduction(assumption,
                            ADD_COMMUTATIVITY.rename(ImmutableMap.of(
                                    "a", B, "b", new Mul(A, B1)
                            ))));
                    for (Impl impl : impls)
                        eqs.add((Eq) impl.getRight());
                    Eq curEq = processEqChain(assumption, eqs);
                    System.err.println("curEq " + curEq);
                    curEq = (Eq) PCalculus.useImplTransitivity(new Impl(assumption, curEq), (Impl) AXIOMS[0].rename(
                            ImmutableMap.of("a", curEq.getLeft(), "b", curEq.getRight()))).getRight();
                    System.err.println("curEq " + curEq);
                    eqs.clear();
                    impls.clear();
                    impls.add(PCalculus.deduction(assumption,
                            AXIOMS[4].rename(ImmutableMap.of("a", new Mul(A1, B), "b", A))));
                    impls.add(new Impl(assumption, curEq));
                    impls.add(PCalculus.deduction(assumption,
                            ((Eq) AXIOMS[4]).reverse().rename(ImmutableMap.of("a", new Mul(A, B1), "b", B))));
                    for (Impl impl : impls)
                        eqs.add((Eq) impl.getRight());
                    System.err.println(
                    );
                    processEqChain(this, Lists.newArrayList(
                            // a' * b' = a'b + a'
                            (Eq) PCalculus.deduction(this,
                                    AXIOMS[7].rename(ImmutableMap.of(
                                            "a", A1, "b", B
                                    ))).getRight(),
                            // a'*b+a'=a*b'+b'
                            processEqChain(assumption, eqs)));

                    induction(base, step, this, B);
                    super.prove();
                }
            };


    public static Eq processEqChain(Node hypo, List<Eq> eqs) {
        Impl impl = null;
        assert eqs.size() > 1;
        for (int i = 0; i < eqs.size() - 1; ++i) {
            // hypo -> A = B
            Impl leftImpl = new Impl(hypo, new Eq((eqs.get(0)).getLeft(),
                    (eqs.get(i)).getRight()));
            // hypo -> B = C
            Impl rightImpl = new Impl(hypo, eqs.get(i + 1));
//            System.err.println(leftImpl);
//            System.err.println(rightImpl);
            impl = PCalculus.deduction(hypo, rightImpl,
                    PCalculus.deduction(hypo, leftImpl,
                            PCalculus.deduction(hypo, TRANSITIVITY.rename(
                                    ImmutableMap.of(
                                            "x", (eqs.get(0)).getLeft(),
                                            "y", (eqs.get(i + 1)).getLeft(),
                                            "z", (eqs.get(i + 1)).getRight())
                            ))
                    ));
        }
        return (Eq) impl.getRight();
    }

    /**
     * b = c -> a * b = a * c
     */
    public static final Impl MUL_SUBST_LEMMA =
            new Impl(new Eq(B, C), new Eq(new Mul(A, B), new Mul(A, C))) {

                @Override
                public void prove() {
                    // b=c-> 0*b=0*c
                    Node base = subst(A, Z);
                    // prove by induction on b that 0 = 0*b
                    Eq prop = new Eq(Z, new Mul(Z, B));
                    Eq baseInBase = new Eq(Z, new Mul(Z, Z));
                    applySymmetry((Eq) AXIOMS[6].rename(ImmutableMap.of(
                            "a", Z
                    )));
                    Impl stepInBase = new Impl(prop, prop.subst(B, B1));
                    // proof of step:

                    List<Impl> chainImpls = Lists.newArrayList(
                            PCalculus.deduction(prop.reverse(), AXIOMS[7].apply(ImmutableMap.of(
                                    "a", Z
                            ), true, true)),
                            PCalculus.deduction(prop.reverse(), ADD_COMMUTATIVITY.rename(ImmutableMap.of(
                                    "a", new Mul(Z, B), "b", Z
                            ))),
                            // 0 * b = 0 -> 0 + 0 * b = 0 + 0
                            (Impl) ADD_SUBST_LEMMA.rename(ImmutableMap.of(
                                    "a", Z, "b", prop.getRight(), "c", prop.getLeft()
                            )),
                            PCalculus.deduction(prop.reverse(), AXIOMS[5].rename(ImmutableMap.of(
                                    "a", Z
                            )))
                    );
                    List<Eq> chainEqs = new ArrayList<>();
                    for (Impl im : chainImpls)
                        chainEqs.add((Eq) im.getRight());
                    PCalculus.useImplTransitivity(
                            PCalculus.useImplTransitivity(
                                    // 0 = 0 * b -> 0 * b = 0
                                    (Impl) SYMMETRY.rename(ImmutableMap.of(
                                            "x", prop.getLeft(), "y", prop.getRight()
                                    )),
                                    // 0 * b = 0 -> 0 * b'  = 0
                                    new Impl(prop.reverse(), processEqChain(prop.reverse(), chainEqs))
                            ), (Impl) SYMMETRY.rename(ImmutableMap.of(
                                    "x", new Mul(Z, B1), "y", Z
                            )));

                    induction(baseInBase, stepInBase, prop, B);
                    Eq eq = new Eq(B, C);
                    // 0= 0*c
                    Eq propC = (Eq) prop.apply(ImmutableMap.of(
                            "b", C
                    ), true, true);
                    // 0 = 0 * b -> 0 = 0 * c -> 0 * b = 0 * c
                    Node axiom = AXIOMS[1].rename(ImmutableMap.of(
                            "a", Z, "b", prop.getRight(), "c", propC.getRight()
                    ));
                    System.out.println(axiom);
                    // b=c->0*b=0*c
                    PCalculus.deduction(eq, PCalculus.MP(axiom, 2));
                    Impl step = new Impl(this, subst(A, A1));
                    //assuming b=c prove a'b = ab+b = ab + c=c + ab
                    // b=c->a'b=ab+b
                    Eq axiomEq = (Eq) PCalculus.deduction(eq, AXIOM_7_ANALOGUE).getRight();
                    List<Eq> eqs = Lists.newArrayList(
                            axiomEq,
                            (Eq) ((Impl) ADD_SUBST_LEMMA.rename(ImmutableMap.of(
                                    "a", new Mul(A, B), "b", B, "c", C
                            ))).getRight(),
                            (Eq) PCalculus.deduction(eq, ADD_COMMUTATIVITY.rename(ImmutableMap.of(
                                    "a", new Mul(A, B), "b", C
                            ))).getRight()
                    );
                    PCalculus.deduction(eq, ADD_SUBST_LEMMA.rename(ImmutableMap.of(
                            "a", C, "b", new Mul(A, B), "c", new Mul(A, C)
                    )));
                    Impl impl = (Impl) PCalculus.SCHEMES[1].apply(ImmutableMap.of(
                            "A", eq, "B", getRight(), "C", new Eq(new Add(C, new Mul(A, B)), new Add(C, new Mul(A, C)))
                    ));
                    System.out.println(impl);
                    Impl axiomImpl = PCalculus.deduction(eq, applySymmetry((Eq) AXIOM_7_ANALOGUE.apply(ImmutableMap.of(
                            "b", C
                    ), true, true)));
                    List<Impl> impls = Lists.newArrayList(
                            // this -> eq -> a'b = c + ab
                            PCalculus.deduction(this, new Impl(eq, processEqChain(eq, eqs))),
                            // this -> eq -> c + ab = c + ac
                            (Impl) PCalculus.MP(PCalculus.reverseImpl(impl)),
                            // this -> eq -> c + ac = ac + c
                            PCalculus.deduction(this, PCalculus.deduction(eq, ADD_COMMUTATIVITY.rename(ImmutableMap.of(
                                    "a", C, "b", new Mul(A, C)
                            )))),
                            // this -> eq -> ac + c = a'c
                            PCalculus.deduction(this, axiomImpl)
                    );
                    eqs.clear();
                    for (Impl im : impls)
                        eqs.add((Eq) ((Impl) im.getRight()).getRight());
                    for (int i = 0; i < impls.size() - 1; i++) {
                        // A = B
                        Eq leftEq = new Eq((eqs.get(0)).getLeft(),
                                (eqs.get(i)).getRight());
                        // B = C
                        Eq rightEq = eqs.get(i + 1);
                        Impl transImpl = (Impl) TRANSITIVITY.rename(ImmutableMap.of(
                                "x", leftEq.getLeft(), "y", leftEq.getRight(), "z", rightEq.getRight()
                        ));
                        PCalculus.deduction(this, eq, leftEq, rightEq, new Eq(leftEq.getLeft(), rightEq.getRight()));
                    }
                    induction(base, step, this, A);
                    super.prove();
                }

            };


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
                    BinaryNode appliedTransB = (BinaryNode) PCalculus.MP(TRANSITIVITY.apply(appMap, true), 2);
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
                    BinaryNode appliedTransC = (BinaryNode) PCalculus.MP(TRANSITIVITY.apply(appMap, true), 2);
                    appMap.clear();
                    appMap.put("x", appliedTransC.getLeft());
                    appMap.put("y", appliedTransC.getRight());
                    // c = 0 + c
                    BinaryNode appliedSym = (BinaryNode) PCalculus.MP(SYMMETRY.rename(appMap));
                    appMap.clear();
                    // b = c -> c = 0 + c
                    PCalculus.MP(PCalculus.SCHEMES[0].apply(ImmutableMap.of(
                            "A", appliedSym, "B", getLeft())));
                    appMap.clear();
                    appMap.put("x", appliedTransB.getLeft());
                    appMap.put("y", appliedTransB.getRight());
                    appMap.put("z", ((BinaryNode) getLeft()).getRight());
                    // b = c -> 0 + b = c
                    BinaryNode bn = (BinaryNode) PCalculus.MP(TRANSITIVITY.apply(appMap, true));
                    appMap.put("x", ((BinaryNode) bn.getRight()).getLeft());
                    appMap.put("y", appliedSym.getLeft());
                    appMap.put("z", appliedSym.getRight());
                    // 0 + b = c -> (c = 0 + c -> 0 + b = 0 + c)
                    bn = (BinaryNode) TRANSITIVITY.apply(appMap, true);
                    appMap.put("A", bn);
                    appMap.put("B", getLeft());
                    // b = c -> 0 + b = c -> (c = 0 + c -> 0 + b = 0 + c)
                    bn = (BinaryNode) PCalculus.MP(PCalculus.SCHEMES[0].apply(appMap));
                    appMap.put("A", getLeft());
                    appMap.put("B", ((BinaryNode) bn.getRight()).getLeft());
                    appMap.put("C", ((BinaryNode) bn.getRight()).getRight());
                    // b = c -> c = 0 + c -> 0 + b = 0 + c
                    PCalculus.MP(PCalculus.SCHEMES[1].apply(appMap), 2);
                    appMap.put("A", getLeft());
                    appMap.put("B", new Eq(C, new Add(Z, C)));
                    appMap.put("C", new Eq(new Add(Z, B), new Add(Z, C)));
                    // b = c -> 0 + b = 0 + c
                    PCalculus.MP(PCalculus.SCHEMES[1].apply(appMap), 2);

                    Impl step = new Impl(this, subst(A, new Inc(A)));
//                    System.out.println("\n\nSTEP = " + step);
                    // a+b=a+c
                    Eq eq = new Eq(new Add(A, B), new Add(A, C));
                    // a+b=a+c -> (a+b)'=(a+c)'
                    Impl cur = (Impl) AXIOMS[0].rename(ImmutableMap.of("a", eq.getLeft(), "b", eq.getRight()));
                    List<Node> eqs = new ArrayList<>();
                    // a+b=a+c->a+b'=(a+b)'
                    eqs.add(PCalculus.deduction(eq, AXIOM_4_ANALOGUE).getRight());
                    eqs.add(cur.getRight());
                    // a' + c = (a + c)'
                    Eq eqC = (Eq) AXIOM_4_ANALOGUE.rename(ImmutableMap.of("a", A, "b", C));
                    System.err.println(eqC);
                    System.err.println(PCalculus.deduction(eq, eqC));
                    // a+b=a+c -> (a + c)' = a' + c
                    eqs.add(PCalculus.deduction(eq,
                            PCalculus.deduction(eq, eqC),
                            PCalculus.deduction(eq,
                                    SYMMETRY.rename(ImmutableMap.of("x", eqC.getLeft(), "y", eqC.getRight()))))
                            .getRight());
                    System.err.println("EQUATIONS");
                    for (Node n : eqs) {
                        System.err.println(n);
                    }
                    // prove (a+b)'=(a+c)' -> a' + b = a' + c by chain of equations
                    Impl impl = null;
                    for (int i = 0; i < eqs.size() - 1; ++i) {
                        // eq -> A = B
                        Impl leftImpl = new Impl(eq, new Eq(((BinaryNode) eqs.get(0)).getLeft(),
                                ((BinaryNode) eqs.get(i)).getRight()));
                        System.err.println(leftImpl);
                        // eq -> B = C
                        Impl rightImpl = new Impl(eq, eqs.get(i + 1));
                        System.err.println(rightImpl);
                        impl = PCalculus.deduction(eq, rightImpl,
                                PCalculus.deduction(eq, leftImpl,
                                        PCalculus.deduction(eq, TRANSITIVITY.rename(
                                                ImmutableMap.of(
                                                        "x", ((BinaryNode) eqs.get(0)).getLeft(),
                                                        "y", ((BinaryNode) eqs.get(i + 1)).getLeft(),
                                                        "z", ((BinaryNode) eqs.get(i + 1)).getRight())
                                        ))
                                ));
                    }
                    Impl right = PCalculus.deduction(new Eq(B, C), impl);
                    impl = (Impl) PCalculus.SCHEMES[1].apply(ImmutableMap.of(
                            "A", new Eq(B, C), "B", new Eq(new Add(A, B), new Add(A, C)),
                            "C", new Eq(new Add(A1, B), new Add(A1, C))));
                    System.out.println(impl);
                    PCalculus.MP(
                            PCalculus.reverseImpl(new Impl(right.getLeft(), ((BinaryNode) right.getRight()).getLeft()),
                                    right, new Impl(right.getLeft(), ((BinaryNode) right.getRight()).getRight())));
//                    // a + b = a + c -> a' + b = a' + c
//                    if (impl != null)
//                        PCalculus.useImplTransitivity(cur, impl);

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
                    PCalculus.MP(AXIOMS[1].apply(map, true), 2);
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
                    PCalculus.MP(new Impl(trueEq, new Impl(sourceEq, trueEq)));
                    map.clear();
                    map.put("A", sourceEq);
                    map.put("B", trueEq);
                    map.put("C", sourceEq.reverse());
                    Impl tautology = (Impl) PCalculus.SCHEMES[1].apply(map);
                    PCalculus.MP(tautology, 2);
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
                    PCalculus.deduction(getLeft(),
                            AXIOMS[1].apply(ImmutableMap.of(
                                    "a", new Var("y"), "b", new Var("x"), "c", new Var("z")), true));
                    Map<String, Node> map = new HashMap<>();
                    map.put("A", getLeft());
                    map.put("B", revEq);
                    map.put("C", getRight());
                    Impl tautology = (Impl) PCalculus.SCHEMES[1].apply(map);
                    PCalculus.MP(tautology, 2);
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
        Node genStep = PCalculus.generalize(step, x);
//        PCalculus.MP(new Impl(step, genStep));
        PCalculus.MP(new Impl(base, new Impl(genStep, new And(base, genStep))), 2);
        PCalculus.MP(new Impl(new And(base, genStep), f));
    }

    static Eq applySymmetry(Eq eq) {
        return (Eq) PCalculus.MP(
                SYMMETRY.apply(ImmutableMap.of("x", eq.getLeft(), "y", eq.getRight()), true));
    }

    static Eq applyTransitivity(Eq first, Eq second) {
        return (Eq) PCalculus.MP(TRANSITIVITY.rename(ImmutableMap.of("x", first.getLeft(),
                "y", first.getRight(), "z", second.getRight())), 2);
    }


}
