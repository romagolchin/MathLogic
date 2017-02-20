import java.util.List;

/**
 * Created by Roman on 20/02/2017.
 */
public class Zero extends ArithmeticOperation {
    public Zero() {
        super(ZERO, null);
    }

    @Override
    int calculate() {
        return 0;
    }
}
