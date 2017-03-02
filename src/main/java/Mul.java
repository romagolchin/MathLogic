import java.util.HashMap;
import java.util.Map;

/**
 * Created by Roman on 19/02/2017.
 */
public class Mul extends BinaryNode implements Term, Calculable {
    public Mul(Node left, Node right) {
        super(FormalArithmetic.MUL, left, right);
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
        Node cur;
        try {
            Node left = getLeft();
            Node right = getRight();
            BinaryNode eq;
            if (FormalArithmetic.Z.equals(right)) {
                System.out.println(new Eq(this, FormalArithmetic.Z));
                return FormalArithmetic.Z;
            } else if (right instanceof Inc
                    && ((Inc) right).getOperand().equals(FormalArithmetic.Z)) {
                Inc rInc = (Inc) right;
                Map<String, Node> map = new HashMap<>();
                map.put("a", left);
                map.put("b", new Inc(((Inc) right).getOperand(), rInc.number - 1));
                eq = (BinaryNode) FormalArithmetic.AXIOMS[7].apply(map);
                System.out.println(eq);
                cur = eq.getRight();

            } else {
                System.out.println("use susbt lemma");
                Node res = ((Calculable) right).calculate();
                Map<String, Node> map = new HashMap<>();
                map.put("a", left);
                map.put("b", right);
                map.put("c", res);
                BinaryNode appliedSubst = (BinaryNode) FormalArithmetic.MUL_SUBST_LEMMA.apply(map);
                // a * c
                cur = ((BinaryNode) PredicateCalculus.MP(appliedSubst)).getRight();
            }
            return ((Calculable) cur).calculate();
        } catch (ClassCastException e) {
            e.printStackTrace();
        }
        return null;
    }
}
