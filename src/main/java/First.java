import parsing.Parser;
import proofs.Checker;

import java.io.*;

/**
 * @author Roman Golchin (romagolchin@gmail.com)
 */
public class First {
    public static void main(String[] args) {
        if (args.length < 2)
            throw new IllegalArgumentException();
        try (BufferedReader reader = new BufferedReader(new FileReader(args[0]))) {
            Parser parser = new Parser(reader);
            try (BufferedWriter writer = new BufferedWriter(
                    new OutputStreamWriter(new FileOutputStream(args[1]), "UTF-8"))) {
                Checker checker = new Checker(parser, writer, false, false, true);
                checker.checkAll();
            } catch (IOException ignored) {

            }
        } catch (IOException ignored) {
        }
    }
}
