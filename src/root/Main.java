package root;

import controller.Game;

public class Main {

    /* @
      @ public behavior
      @ ensures (\forall int i; 0 <= i && i < args.length; args[i] != null); // Garante que os argumentos não são nulos
      @ signals (Exception e) true; // Permite lançar qualquer exceção
      @ */
    public static void main(String[] args) {
        new Game();
    }
}
