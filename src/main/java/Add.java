
import java.util.HashMap;
import java.util.Map;

/**
 * Created by Roman on 24/02/2017.
 */
public class Add extends BinaryNode implements Term, Calculable {
    public Add(Node left, Node right) {
        super(Arithmetic.ADD, left, right);
        priority = 5;
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
//        System.out.println("Add");
        Node cur;
        try {
            Node left = getLeft();
            Node right = getRight();
            BinaryNode eq;
            if (right.equals(Arithmetic.Z))
                right = new Inc(Arithmetic.Z, 0);
            if (((Calculable) right).isCalculated()) {
                Map<String, Node> map = new HashMap<>();
                map.put("a", left);
                eq = (BinaryNode) Arithmetic.AXIOMS[5].rename(map);
                System.out.println(eq);
                for (int i = 1; i <= ((Inc) right).number; ++i) {
                    map.clear();
                    map.put("a", left);
                    map.put("b", new Inc(Arithmetic.Z, i - 1));
//                    System.out.println("use axiom 4");
//                    System.out.println(map.size());
                    eq = (BinaryNode) Arithmetic.AXIOMS[4].rename(map);
                    Node x = eq.getLeft();
                    Node y = eq.getRight();
                    System.out.println(eq);
                    map.put("a", new Add(getLeft(), new Inc(Arithmetic.Z, i - 1)));
                    map.put("b", i == 1 ? getLeft() : new Inc(getLeft(), i - 1));
                    eq = (BinaryNode) PCalculus.MP(Arithmetic.AXIOMS[0].rename(map));
                    Node z = eq.getRight();
                    map.clear();
//                    System.out.println("use transitivity");
                    map.put("x", x);
                    map.put("y", y);
                    map.put("z", z);
                    PCalculus.MP(Arithmetic.TRANSITIVITY.apply(map, true), 2);
                }
                cur = eq.getRight();

            } else {
                Node res = ((Calculable) right).calculate();
//                System.out.println("use susbt add lemma");
//                System.out.println("res = " + res);
                System.err.println(res);
//                assert (((Calculable) res).isCalculated());
                Map<String, Node> map = new HashMap<>();
                map.put("a", left);
                map.put("b", right);
                map.put("c", res);
                BinaryNode appliedSubst = (BinaryNode) Arithmetic.ADD_SUBST_LEMMA.rename(map);
                // a + c
                cur = ((BinaryNode) PCalculus.MP(appliedSubst)).getRight();
            }
//            System.out.println("this = cur " + this + " " + cur);
//            System.out.println("cur = calc cur " + cur + " " + ((Calculable) cur).calculate());
            if (((Calculable) cur).isCalculated())
                return cur;
            return Arithmetic.applyTransitivity(new Eq(this, cur), new Eq(cur, ((Calculable) cur).calculate()))
                    .getRight();
        } catch (ClassCastException e) {
            e.printStackTrace();
        }
        return null;
    }

    @Override
    public String toString() {
        String rs = getRight().toString();
        String ls = getLeft().toString();
        if (getRight().priority <= priority) {
            rs = "(" + rs + ")";
        }
        if (getLeft().priority < priority) {
            ls = "(" + ls + ")";
        }
        return ls + name + rs;
    }
}
