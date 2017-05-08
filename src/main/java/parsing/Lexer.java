package parsing;

import com.google.common.collect.BiMap;
import com.google.common.collect.ImmutableBiMap;

import java.util.*;

/**
 * @author Roman Golchin (romagolchin@gmail.com)
 */
public class Lexer {
    private String s;
    public static final BiMap<Character, Token> tokenMap = ImmutableBiMap.<Character, Token>builder()
            .put('|', Token.OR)
            .put('&', Token.AND)
            .put('!', Token.NOT)
            .put('+', Token.ADD)
            .put('*', Token.MUL)
            .put('=', Token.EQ)
            .put('\'', Token.INC)
            .put('@', Token.FORALL)
            .put('?', Token.EXISTS)
            .put('(', Token.OPEN)
            .put(')', Token.CLOSE)
            .put(',', Token.COMMA)
            .put('0', Token.ZERO).build();
    public static final Map<Token, Character> charMap = tokenMap.inverse();
    int pos;
    String pred;
    String var;
    Token token;

    public Lexer(String s) {
        pos = 0;
        this.s = s;
        next();
    }


    public void next() {
//        System.err.println("pos = " + pos);
        if (pos >= s.length()) {
            token = Token.END;
            return;
        }
        token = null;
        if (pos < s.length() - 1) {
            String substring = s.substring(pos, pos + 2);
            if (substring.equals("|-"))
                this.token = Token.PROV;
            else if (substring.equals("->"))
                this.token = Token.IMPL;
        }
        if (this.token != null) {
            pos += 2;
            return;
        }
        char ch = s.charAt(pos);
        Token token = tokenMap.get(ch);
        if (token != null) {
            this.token = token;
            pos++;
            return;
        }
        if (Character.isLetter(ch)) {
            int i;
            for (i = pos + 1; i < s.length() && Character.isDigit(s.charAt(i)); i++);
            if (Character.isUpperCase(ch)) {
                this.token = Token.PRED;
                pred = s.substring(pos, i);
            }
            else {
                this.token = Token.VAR;
                var = s.substring(pos, i);
            }
            pos = i;
        }
        if (this.token == null)
            throw new IllegalArgumentException("unable to get token at position " + pos);
    }
}
