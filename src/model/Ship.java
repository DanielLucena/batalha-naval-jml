package model;

public abstract class Ship {

    public final int length;
    public final String name;

    /*@ invariant length >= 0; */
    
    /*@ requires name != null; */
    /*@ requires length >= 0; */
    /*@ ensures this.name.equals(name); */
    /*@ ensures this.length == length; */
    public Ship (String name, int length) {
        this.length = length;
        this.name = name;
    }
}
