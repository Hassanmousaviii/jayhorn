package soottocfg.cfg.type;

public class DoubleType extends PrimitiveType {

    /**
     *
     */
    // TODO: This is a random number distinct from other serialVersionUIDs. Is this the intended value?
    private static final long serialVersionUID = -5047164968046256817L;
    private static final DoubleType instance = new DoubleType();

    public static DoubleType instance() {
        return instance;
    }

    /**
     *
     */
    private DoubleType() {
        // TODO Auto-generated constructor stub
    }

    public String toString() {
        return "Double";
    }
}
