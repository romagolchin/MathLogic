
import com.google.common.collect.ImmutableMap;

import java.io.BufferedOutputStream;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.PrintStream;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;


/**
 * Created by Roman on 19/02/2017.
 */
public class Main {
    public static void main(String[] args) throws FileNotFoundException {
        try (PrintStream stream = new PrintStream(new BufferedOutputStream(
                new FileOutputStream(args.length > 1 ? args[1] : "proof")))) {
            System.setOut(stream);
            System.out.println("|-" + FormalArithmetic.ADD_COMMUTATIVITY);
            Node truth = PredicateCalculus.SCHEMES[0].apply(ImmutableMap.of(
                    "A", new Eq(FormalArithmetic.Z, FormalArithmetic.Z),
                    "B", new Eq(FormalArithmetic.Z, FormalArithmetic.Z)
            ));
            System.out.println(truth);
            final int N = 101;
            final int index = (args.length > 0) ? Integer.valueOf(args[0]) : (N - 1);
            Inc[] nums = new Inc[N];
            for (int i = 0; i < N; ++i) {
                nums[i] = new Inc(FormalArithmetic.Z, i);
            }
            Calculable[] toCalc = new Calculable[]{
//                    new Add(new Add(nums[1], new Mul(nums[3],
//                            nums[2])), nums[1]), new Add(nums[0], nums[0]),
//                    new Add(nums[0], nums[5])
                    new Mul(new Add(nums[index], nums[1]), new Add(nums[index], nums[1]))
                    , new Add(new Add(new Mul(nums[index], nums[index]), new Mul(nums[2], nums[index])), nums[1])
            };
            for (Node ax : FormalArithmetic.AXIOMS) {
                System.out.println(ax);
                PredicateCalculus.generalize(ax, ax.getVars(), true);

            }
//            System.out.println(FormalArithmetic.SYMMETRY.rename(new HashMap<String, Node>() {{
//                put("x", new Mul(new Var("x"), new Var("y")));
//                put("y", new Add(new Var("x"), new Var("y")));
//            }}));
            FormalArithmetic.REFLEXIVITY.prove();
            FormalArithmetic.SYMMETRY.prove();
            for (Node ax : FormalArithmetic.AXIOMS) {
                if (ax instanceof Eq) {
                    Eq eq = (Eq) ax;
                    PredicateCalculus.generalize(FormalArithmetic.applySymmetry(eq), true);
                }
            }
            FormalArithmetic.TRANSITIVITY.prove();
            FormalArithmetic.AXIOM_4_ANALOGUE.prove();
            FormalArithmetic.ADD_COMMUTATIVITY.prove();
//            System.err.println(FormalArithmetic.AXIOMS[5]);
//            System.err.println(FormalArithmetic.AXIOMS[5].subst(FormalArithmetic.A, FormalArithmetic.Z)
//            .subst(FormalArithmetic.B, FormalArithmetic.Z)
//            );
//            System.out.println("subst add");
            FormalArithmetic.ADD_SUBST_LEMMA.prove();
//            System.out.println("ref");
//            System.out.println("sym");
//            System.out.println("trans");
//            for (Calculable c : toCalc) {
//                System.out.println(c.calculate());
//                System.out.println("----------------------------------------------");
//            }
//            FormalArithmetic.AXIOMS[0].apply(new HashMap<String, Node>(){{
//                put("a", new Mul(nums[2], nums[3]));
//                put("b", nums[6]);
//            }}, true);
//            PredicateCalculus.generalize(new Eq(new Var("a"), new Var("a")),
//                    new Var("a"));
        }
    }
}
