/**
 * Created by Roman on 19/02/2017.
 */
public enum ArithmeticFunctionalSymbol {
    ZERO(0),
    INC(1),
    MUL(2),
    ADD(2);

    ArithmeticFunctionalSymbol(int numArgs) {
        this.numArgs = numArgs;
    }

    int numArgs;
}
