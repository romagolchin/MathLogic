/**
 * Created by Roman on 24/02/2017.
 */
public interface Calculable {
    Node calculate();
    default boolean isCalculated() {
        return false;
    }
}
