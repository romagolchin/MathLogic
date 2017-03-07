import com.google.common.collect.ImmutableMap;

import java.util.HashMap;
import java.util.Map;

/**
 * Created by Roman on 19/02/2017.
 */
public class Mul extends BinaryNode implements Term, Calculable {
    public Mul(Node left, Node right) {
        super(Arithmetic.MUL, left, right);
        priority = 6;
    }

    public Mul(Node toCopy) {
        super(toCopy);
    }

    @Override
    protected Node copy() {
        return new Mul(this);
    }

    @Override
    public Node calculate() {
//        System.out.println("Mul");
        Node cur;
        try {
            Node left = getLeft();
            Node right = getRight();
            BinaryNode eq;
            if (Arithmetic.Z.equals(right)) {
                System.out.println(
                        Arithmetic.AXIOMS[6].rename(ImmutableMap.of(
                                "a", left
                        ))
                );
                return Arithmetic.Z;
            } else if (right instanceof Inc
                    && ((Inc) right).getOperand().equals(Arithmetic.Z)) {
                Inc rInc = (Inc) right;
                Map<String, Node> map = new HashMap<>();
                map.put("a", left);
                map.put("b", new Inc(((Inc) right).getOperand(), rInc.number - 1));
                eq = (BinaryNode) Arithmetic.AXIOMS[7].rename(map);
                System.out.println(eq);
                cur = eq.getRight();

            } else {
                Node res = ((Calculable) right).calculate();
//                System.out.println("res = " + res);
//                System.out.println("use susbt mul lemma");
                assert (((Calculable) res).isCalculated());
//                System.out.println(left + " " + right + " " + res);
                Map<String, Node> map = new HashMap<>();
                map.put("a", left);
                map.put("b", right);
                map.put("c", res);
                BinaryNode appliedSubst = (BinaryNode) Arithmetic.MUL_SUBST_LEMMA.rename(map);
                // a * c
                cur = ((BinaryNode) PCalculus.MP(appliedSubst)).getRight();
            }
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
