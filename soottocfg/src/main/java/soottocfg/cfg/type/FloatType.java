package soottocfg.cfg.type;

public class FloatType extends PrimitiveType{
    /**
     *
     */
    // TODO: This is a random number distinct from other serialVersionUIDs. Is this the intended value?
    private static final long serialVersionUID = -5047164968046256817L;
    private static final FloatType instance = new FloatType();

    public static FloatType instance() {
        return instance;
    }

    /**
     *
     */
    private FloatType() {
        // TODO Auto-generated constructor stub
    }

    public String toString() {
        return "Float";
    }
}
