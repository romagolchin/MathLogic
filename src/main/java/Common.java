import parsing.Parser;
import proofs.Checker;

import java.io.*;
import java.nio.charset.StandardCharsets;

/**
 * @author Roman Golchin (romagolchin@gmail.com)
 */
public class Common {
    final boolean strict;
    final boolean deduction;
    final boolean annotation;

    public Common(boolean strict, boolean deduction, boolean annotation) {
        this.strict = strict;
        this.deduction = deduction;
        this.annotation = annotation;
    }

    public void solve(String[] args) {
        if (args.length < 2)
            throw new IllegalArgumentException();
        try (BufferedReader reader = new BufferedReader(new FileReader(args[0]))) {
            Parser parser = new Parser(reader);
            try (BufferedWriter writer = new BufferedWriter(
                    new OutputStreamWriter(new FileOutputStream(args[1]), StandardCharsets.UTF_8))) {
                Checker checker = new Checker(parser, writer, strict, deduction, annotation);
                checker.checkAll();
            } catch (IOException ignored) {
                ignored.printStackTrace();
            }
        } catch (IOException ignored) {
            ignored.printStackTrace();
        }
    }
}
