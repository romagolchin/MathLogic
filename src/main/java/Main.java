
import com.google.common.collect.ImmutableMap;

import java.io.*;


/**
 * Created by Roman on 19/02/2017.
 */
public class Main {
    public static void main(String[] args) throws FileNotFoundException {
        String inFile = args.length > 0 ? args[0] : "input";
        try (BufferedReader reader = new BufferedReader(new FileReader(inFile))) {
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

                Arithmetic.TRANSITIVITY.prove();
                Arithmetic.AXIOM_4_ANALOGUE.prove();
                Arithmetic.ADD_COMMUTATIVITY.prove();
                Arithmetic.ADD_SUBST_LEMMA.prove();
                Arithmetic.ADD_ASSOCIATIVITY.prove();
                Arithmetic.AXIOM_7_ANALOGUE.prove();
                Arithmetic.MUL_SUBST_LEMMA.prove();


                Node[] results = new Node[toCalc.length];
                for (int i = 0; i < toCalc.length; i++) {
                    Calculable c = toCalc[i];
                    if (c instanceof Node) {
                        Node n = (Node) c;
                        Node calculated = c.calculate();
                        Arithmetic.applySymmetry(new Eq(n, calculated));
                        results[i] = calculated;
                    }
                }
                PCalculus.MP(Arithmetic.AXIOMS[1].rename(ImmutableMap.of(
                        "a", results[0], "b", (Node) toCalc[0], "c", (Node) toCalc[1]
                )), 2);
            }
        } catch (IOException e) {
        }
    }
}
