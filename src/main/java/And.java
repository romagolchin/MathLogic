/**
 * Created by Roman on 24/02/2017.
 */
public class And extends BinaryNode {
    public And(Node left, Node right) {
        super(PCalculus.AND, left, right);
        priority = 2;
    }
}
