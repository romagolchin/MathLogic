import parsing.Parser;
import proofs.Checker;

import java.io.*;

/**
 * Usage: First &lt;inFile&gt; &lt;outFile&gt; &lt;deductionNeeded&gt;
 * @author Roman Golchin (romagolchin@gmail.com)
 */
public class Second {

    public static void main(String[] args) {
        if (args.length < 2)
            throw new IllegalArgumentException();
        try (BufferedReader reader = new BufferedReader(new FileReader(args[0]))) {
            Parser parser = new Parser(reader);
            try (BufferedWriter writer = new BufferedWriter(new OutputStreamWriter(new FileOutputStream(args[1]), "UTF-8"))) {
                Checker checker = new Checker(parser, writer, true, args.length == 2 || Integer.valueOf(args[2]) != 0, false);
                checker.checkAll();
            } catch (IOException ignored) {
            }
        } catch (IOException ignored) {
        }
    }
}
