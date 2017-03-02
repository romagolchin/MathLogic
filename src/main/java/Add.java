
import java.util.HashMap;
import java.util.Map;

/**
 * Created by Roman on 24/02/2017.
 */
public class Add extends BinaryNode implements Term, Calculable {
    public Add(Node left, Node right) {
        super(FormalArithmetic.ADD, left, right);
        priority = 1;
    }

    public Add(Node toCopy) {
        super(toCopy);
    }

    @Override
    protected Node copy() {
        return new Add(this);
    }

    @Override
    public Node calculate() {
        Node cur;
        try {
            Node left = getLeft();
            Node right = getRight();
            BinaryNode eq;
            if (right.equals(FormalArithmetic.Z))
                right = new Inc(FormalArithmetic.Z, 0);
            if (((Calculable) right).isCalculated()) {
                Map<String, Node> map = new HashMap<>();
                map.put("a", left);
                eq = (BinaryNode) FormalArithmetic.AXIOMS[5].apply(map);
                System.out.println(eq);
                map.clear();
                for (int i = 1; i <= ((Inc) right).number; ++i) {
                    map.put("a", left);
                    map.put("b", new Inc(FormalArithmetic.Z, i - 1));
                    eq = (BinaryNode) FormalArithmetic.AXIOMS[4].apply(map);
                    Node x = eq.getLeft();
                    Node y = eq.getRight();
                    System.out.println(eq);
                    map.put("a", new Add(getLeft(), new Inc(FormalArithmetic.Z, i - 1)));
                    map.put("b", i == 1 ? getLeft() : new Inc(getLeft(), i - 1));
                    eq = (BinaryNode) PredicateCalculus.MP(FormalArithmetic.AXIOMS[0].apply(map));
                    Node z = eq.getRight();
                    map.clear();
                    System.out.println("use transitivity");
                    map.put("x", x);
                    map.put("y", y);
                    map.put("z", z);
                    FormalArithmetic.TRANSITIVITY.apply(map, true);
                }
                cur = eq.getRight();

            } else {
                System.out.println("use susbt add lemma");
                Node res = ((Calculable) right).calculate();
                Map<String, Node> map = new HashMap<>();
                map.put("a", left);
                map.put("b", right);
                map.put("c", res);
                BinaryNode appliedSubst = (BinaryNode) FormalArithmetic.ADD_SUBST_LEMMA.apply(map);
                // a + c
                cur = ((BinaryNode) PredicateCalculus.MP(appliedSubst)).getRight();
            }
            return ((Calculable) cur).calculate();
        } catch (ClassCastException e) {
            e.printStackTrace();
        }
        return null;
    }
}
