
import com.google.common.collect.ImmutableMap;

import java.io.*;


/**
 * Created by Roman on 19/02/2017.
 */
public class Main {
    public static void main(String[] args) throws FileNotFoundException {
        try (BufferedReader reader = new BufferedReader(new FileReader("input"))) {
            int index = Integer.valueOf(reader.readLine());
            System.err.println(index);
            try (PrintStream stream = new PrintStream(new BufferedOutputStream(
                    new FileOutputStream(args.length > 1 ? args[1] : "proof")))) {
                System.setOut(stream);
                final int N = 101;
                Inc[] nums = new Inc[N];
                for (int i = 0; i < N; ++i) {
                    nums[i] = new Inc(Arithmetic.Z, i);
                }
                Calculable[] toCalc = new Calculable[]{
//                    new Add(new Add(nums[1], new Mul(nums[3],
//                            nums[2])), nums[1]), new Add(nums[0], nums[0]),
//                        nums[3],
//                        new Add(nums[2], nums[1]),
                        new Mul(new Add(nums[index], nums[1]), new Add(nums[index], nums[1]))
                        , new Add(new Add(new Mul(nums[index], nums[index]), new Mul(nums[2], nums[index])), nums[1])
//                        , new Mul(nums[2], new Add(nums[2], nums[1]))
                };
                System.out.println("|-" + new Eq((Node) toCalc[0], (Node) toCalc[1] ));
                Node truth = PCalculus.SCHEMES[0].apply(ImmutableMap.of(
                        "A", new Eq(Arithmetic.Z, Arithmetic.Z),
                        "B", new Eq(Arithmetic.Z, Arithmetic.Z)
                ));
                System.out.println(truth);

                for (Node ax : Arithmetic.AXIOMS) {
                    System.out.println(ax);
                    PCalculus.generalize(ax, ax.getVars(), true);

                }
                Arithmetic.REFLEXIVITY.prove();
                Arithmetic.SYMMETRY.prove();
                for (Node ax : Arithmetic.AXIOMS) {
                    if (ax instanceof Eq) {
                        Eq eq = (Eq) ax;
                        PCalculus.generalize(Arithmetic.applySymmetry(eq), true);
                    }
                }

//                Var A = Arithmetic.A;
//                Inc A1 = Arithmetic.A1;
//                Var B = Arithmetic.B;
//                Inc B1 = Arithmetic.B1;
//                Var C = Arithmetic.C;
//
//                Impl im = new Impl(new Eq(new Var("x"), new Var("y")),
//                    new Impl(new Eq(new Var("x"), new Var("z")),
//                            new Eq(new Var("y"), new Var("z"))));
//                Node applied = im.apply(ImmutableMap.of(
//                        "x", new Inc(new Add(A, B)),
//                        "y", new Add(A, B1),
//                        "z", new Add(A1, B)
//
//                ), true);
//                System.out.println(applied);
//                Node semiApplied = im.subst(new Var("z"), new Add(A1, B));
//                System.out.println(semiApplied);
//                System.out.println((semiApplied).subst(new Var("y"),
//                        new Add(A, new Inc(B1, 3))));
                Arithmetic.TRANSITIVITY.prove();
                Arithmetic.AXIOM_4_ANALOGUE.prove();
                Arithmetic.ADD_COMMUTATIVITY.prove();
                Arithmetic.ADD_SUBST_LEMMA.prove();
                Arithmetic.ADD_ASSOCIATIVITY.prove();
                Arithmetic.AXIOM_7_ANALOGUE.prove();
                Arithmetic.MUL_SUBST_LEMMA.prove();


//                Var Z = Arithmetic.Z;
//                Eq alpha = new Eq(Z, Z);
//                Eq beta = new Eq(new Inc(Z), new Inc(Z));
//                Eq gamma1 = new Eq(new Add(nums[2], nums[2]), new Mul(nums[2], nums[2]));
//                Eq gamma2 = new Eq(new Mul(nums[2], nums[2]), nums[4]);
//                Eq gamma3 = new Eq(new Add(nums[2], nums[2]), nums[4]);
//                System.out.println(new Impl(gamma1, new Impl(gamma2, gamma3)));
//                System.out.println(new Impl(alpha, new Impl(beta, gamma1)));
//                System.out.println(new Impl(alpha, new Impl(beta, gamma2)));
//                PCalculus.deduction(alpha, beta, gamma1, gamma2, gamma3);


//                System.out.println(
//                        new Add(Arithmetic.Z, new Add(Arithmetic.Z, Arithmetic.Z)));
//                System.out.println(
//                        new Add(new Add(Arithmetic.Z, Arithmetic.Z), Arithmetic.Z));
                Node[] results = new Node[toCalc.length];
                for (int i = 0; i < toCalc.length; i++) {
                    Calculable c = toCalc[i];
//                    System.out.println(
                    if (c instanceof Node) {
                        Node n = (Node) c;
                        Node calculated = c.calculate();
                        Arithmetic.applySymmetry(new Eq(n, calculated));
                        results[i] = calculated;
                    }
//                    );
//                    System.out.println("----------------------------------------------");
                }
                PCalculus.MP(Arithmetic.AXIOMS[1].rename(ImmutableMap.of(
                        "a", results[0], "b", (Node) toCalc[0], "c", (Node) toCalc[1]
                )), 2);
//                System.out.println(Arithmetic.AXIOMS[4].apply(
//                        ImmutableMap.of("a", nums[2], "b", nums[3])
//                ));
//                System.out.println(Arithmetic.AXIOMS[7].apply(
//                        ImmutableMap.of("a", nums[2], "b", nums[3])
//                ));
//
//
//                Arithmetic.MUL_SUBST_LEMMA.rename(ImmutableMap.of(
//                        "a", nums[3], "b", new Add(nums[1], nums[1]), "c", nums[2]
//                ));

//            System.out.println("----------------------------------------------");
//            System.out.println(new Mul(new Add(nums[2], nums[1]), new Add(nums[2], nums[3])));
//            PCalculus.reverseImpl(new Eq(nums[0], nums[0]), new Eq(nums[0], nums[1]),
//                    new Eq(nums[0], nums[2]));
//            Arithmetic.AXIOMS[0].apply(new HashMap<String, Node>(){{
//                put("a", new Mul(nums[2], nums[3]));
//                put("b", nums[6]);
//            }}, true);
//            PCalculus.generalize(new Eq(new Var("a"), new Var("a")),
//                    new Var("a"));
            }
        } catch (IOException e) {
        }
    }
}
