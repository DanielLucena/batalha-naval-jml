package model;

public abstract class Ship {

    /*@ invariant name != null; */
    /*@ invariant length >= 0 && length <= 10000; */

    public final int length;
    public final String name;
    
    /*@ requires name != null; */
    /*@ requires length >= 0 && length <= 10000; */
    /*@ ensures this.name.equals(name); */
    /*@ ensures this.length == length; */
    public Ship (String name, int length) {
        this.length = length;
        this.name = name;
    }

    /*@
      ensures \result.equals(name);
      pure
    @*/
    public String getName() {
        return name;
    }

    /*@
      ensures \result == length;
      pure
    @*/
    public int getLength() {
        return length;
    }
}
