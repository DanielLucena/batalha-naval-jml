package model;

public class Submarine extends Ship {
    /*@
        ensures getName().equals("Submarine") && getLength() == 1;
        ensures getLength() == 1;
    @*/
    public Submarine () {
        super("Submarine", 1);
    }
}
