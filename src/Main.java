import java.io.BufferedOutputStream;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.PrintStream;
import java.util.ArrayList;
import java.util.List;

/**
 * Created by Roman on 19/02/2017.
 */
public class Main {
    public static void main(String[] args) {
//        List<Number> numbers = new ArrayList<>();
//        numbers.add(0);
//        Integer x = (Integer) numbers.get(0);
        try(PrintStream stream = new PrintStream(new BufferedOutputStream(
                new FileOutputStream("out")))) {
            System.setOut(stream);
        } catch (FileNotFoundException e) {
            // ignore
        }
    }
}
