package jayhorn.hornify.encoder;

import java.io.Console;
import java.math.BigInteger;

public class IeeeFloatt {
    rounding_modet rounding_mode;
    private boolean signFlag;
    private BigInteger exponent;
    private BigInteger fraction;
    private boolean NaNFlag;
    private boolean infinityFlag;
    private IeeeFloatSpect spec;

    Boolean NaN_flag, infinity_flag, sign_flag;;

    enum rounding_modet
    {
        ROUND_TO_EVEN,
        ROUND_TO_AWAY,
        ROUND_TO_PLUS_INF,
        ROUND_TO_MINUS_INF,
        ROUND_TO_ZERO,
        UNKNOWN,
        NONDETERMINISTIC
    } ;

    public IeeeFloatt() {
        rounding_mode = rounding_modet.ROUND_TO_EVEN;
        signFlag = false;
        exponent = new BigInteger("0");
        fraction = new BigInteger("0");
        NaNFlag = false;
        infinityFlag = false;
    }
    public IeeeFloatt(IeeeFloatSpect s) {
        rounding_mode = rounding_modet.ROUND_TO_EVEN;
        spec = s;
        signFlag = false;
        exponent = new BigInteger("0");
        fraction = new BigInteger("0");
        NaNFlag = false;
        infinityFlag = false;
    }
    BigInteger get_exponent()
    {
        return exponent;
    }

    BigInteger get_fraction()
    {
        return fraction;
    }

    Boolean get_sign(){return signFlag;}
    public void makeNaN() {
        NaN_flag = true;
        //sign=false;
        exponent = BigInteger.ZERO;
        fraction = BigInteger.ZERO;
        infinity_flag = false;
    }
    void make_fltmax()
    {
        BigInteger bit_pattern = new BigInteger("2").pow(spec.e + spec.f).subtract(BigInteger.valueOf(1)).subtract(new BigInteger("2").pow(spec.f));
        unpack(bit_pattern);
    }
    void divide_and_round(BigInteger fraction, BigInteger factor)
    {
        BigInteger remainder = fraction.mod(factor);// fraction % factor;
        fraction = fraction.divide(factor); //fraction /= factor;

        if (remainder.compareTo(BigInteger.valueOf(0)) != 0) //remainder != 0
        {
            switch (rounding_mode)
            {
                case ROUND_TO_EVEN:
                {
                    BigInteger factor_middle =  factor.divide(BigInteger.valueOf(2));//factor / 2;
                    if (remainder.compareTo(factor_middle) == -1) //remainder < factor_middle
                    {
                        // crop
                    }
                    else if (remainder.compareTo(factor_middle) == 1 ) //remainder > factor_middle
                    {
                        fraction.add(BigInteger.valueOf(1));//++fraction;
                    }
                    else // exactly in the middle -- go to even
                    {
                        if (fraction.mod(BigInteger.valueOf(2)).compareTo(BigInteger.valueOf(0)) != 0) //(fraction % 2) != 0
                            fraction.add(BigInteger.valueOf(1));//++fraction;
                    }
                }
                break;

                case ROUND_TO_ZERO:
                    // this means just crop
                    break;

                case ROUND_TO_MINUS_INF:
                    if (sign_flag)
                        fraction.add(BigInteger.valueOf(1));//++fraction;
                    break;

                case ROUND_TO_PLUS_INF:
                    if (!sign_flag)
                        fraction.add(BigInteger.valueOf(1));//++fraction;
                    break;

                default:
                    assert(false);
            }
        }
    }
    public void unpack(BigInteger i) {
        assert spec.f != 0;
        assert spec.e != 0;

        BigInteger tmp = i;

        // split this apart
        BigInteger pf = new BigInteger("2").pow(spec.f);
        fraction = tmp.mod(pf);
        tmp = tmp.divide(pf);

        BigInteger pe = new BigInteger("2").pow(spec.e);
        exponent = tmp.mod(pe);
        tmp = tmp.divide(pe);

        signFlag = (i.signum() == -1);//!tmp.equals(new BigInteger("0"));

        // NaN?
        if (exponent.equals(spec.maxExponent()) && !fraction.equals(new BigInteger("0"))) {
            makeNaN();
        } else if (exponent.equals(spec.maxExponent()) && fraction.equals(new BigInteger("0"))) { // Infinity
            NaNFlag = false;
            infinityFlag = true;
        } else if (exponent.equals(new BigInteger("0")) && fraction.equals(new BigInteger("0"))) { // zero
            NaNFlag = false;
            infinityFlag = false;
        } else if (exponent.equals(new BigInteger("0"))) { // denormal?
            NaNFlag = false;
            infinityFlag = false;
            exponent = spec.bias().negate().add(new BigInteger("1")); // NOT -spec.bias()!
        } else { // normal
            NaNFlag = false;
            infinityFlag = false;
            fraction = fraction.add(new BigInteger("2").pow(spec.f)); // hidden bit!
            double fr = fraction.doubleValue();
            exponent = exponent.subtract(spec.bias()); // un-bias
        }
    }
    public boolean isNormal() {
        return !NaNFlag && fraction.compareTo(new BigInteger("2").pow(spec.f)) >= 0;
    }
    public BigInteger pack() {
        BigInteger result = new BigInteger("0");

        // sign bit
        if (signFlag) {
            result = result.add( new BigInteger("2").pow(spec.e + spec.f));
        }

        if (NaNFlag) {
            result = result.add(new BigInteger("2").pow(spec.f).multiply(spec.maxExponent()));
            result = result.add(new BigInteger("1"));
        } else if (infinityFlag) {
            result = result.add(new BigInteger("2").pow(spec.f).multiply(spec.maxExponent()));
        } else if (fraction.equals(new BigInteger("0")) && exponent.equals(new BigInteger("0"))) {
            // do nothing
        } else if (isNormal()) { // normal?
            // fraction -- need to hide hidden bit
            result = result.add(fraction.subtract(new BigInteger("2").pow(spec.f))); // hidden bit

            // exponent -- bias!
            result = result.add(new BigInteger("2").pow(spec.f).multiply(exponent.add(spec.bias())));
        } else { // denormal
            result = result.add(fraction); // denormal -- no hidden bit
            // the exponent is zero
        }

        return result;
    }
    public void align() {
        // NaN?
        if (NaN_flag) {
            fraction = BigInteger.valueOf(0);
            exponent = BigInteger.valueOf(0);
            sign_flag = false;
            return;
        }

        // do sign
        if (fraction.compareTo(BigInteger.valueOf(0)) == -1) { // fraction < 0
            sign_flag = !sign_flag;
            fraction = fraction.negate();
        }

        // zero?
        if (fraction.compareTo(BigInteger.valueOf(0)) == 0) { //fraction == 0
            exponent = BigInteger.valueOf(0);
            return;
        }

        BigInteger f_power = new BigInteger("2").pow(spec.f);
        BigInteger f_power_next = new BigInteger("2").pow(spec.f + 1);

        int lowPower2 = 0;//floorPow2(fraction);

        BigInteger exponent_offset = new BigInteger("0");

        if (lowPower2 < spec.f) { // too small
            exponent_offset.subtract(BigInteger.valueOf(spec.f - lowPower2));

            assert fraction.multiply(new BigInteger("2").pow(spec.f - lowPower2)).compareTo(f_power) >= 0;
            assert fraction.multiply(new BigInteger("2").pow(spec.f - lowPower2)).compareTo(f_power_next) < 0;
        } else if (lowPower2 > spec.f) { // too large
            exponent_offset.add(BigInteger.valueOf(lowPower2 - spec.f));

            assert fraction.divide(new BigInteger("2").pow(lowPower2 - spec.f)).compareTo(f_power) >= 0;
            assert fraction.divide(new BigInteger("2").pow(lowPower2 - spec.f)).compareTo(f_power_next) < 0;
        }

        BigInteger biased_exponent = exponent_offset.add(exponent).add(spec.bias());
        // exponent too large (infinity)?
        if (biased_exponent.compareTo(spec.maxExponent()) >= 0) { //biased_exponent >= spec.maxExponent()
            // we need to consider the rounding mode here
            switch (rounding_mode) {
                case UNKNOWN:
                case NONDETERMINISTIC:
                case ROUND_TO_EVEN:
                    infinity_flag = true;
                    break;
                case ROUND_TO_MINUS_INF:
                    // the result of the rounding is never larger than the argument
                    if (sign_flag)
                        infinity_flag = true;
                    else
                        make_fltmax();
                    break;
                case ROUND_TO_PLUS_INF:
                    // the result of the rounding is never smaller than the argument
                    if (sign_flag) {
                        make_fltmax();
                        sign_flag = true; // restore sign
                    } else
                        infinity_flag = true;
                    break;
                case ROUND_TO_ZERO:
                    if (sign_flag) {
                        make_fltmax();
                        sign_flag = true; // restore sign
                    } else
                        make_fltmax(); // positive
                    break;
                default:
                    assert false;
            }
            return; // done
        }
        if (biased_exponent.compareTo(new BigInteger("0")) <= 0) { // exponent too small?
            // produce a denormal (or zero)
            BigInteger new_exponent = new BigInteger("1").subtract(spec.bias());
            exponent_offset = new_exponent.subtract(exponent);
        }

        exponent.add(exponent_offset); //+= exponent_offset.intValue();

        if (exponent_offset.intValue() > 0) {
            divide_and_round(fraction, new BigInteger("2").pow(exponent_offset.intValue()));

            // rounding might make the fraction too big!
            if (fraction.compareTo(f_power_next) == 0 /*fraction == f_power_next.intValue()*/) { // fraction == f_power_next
                fraction = f_power;//.intValue();
                exponent.add(BigInteger.valueOf(1));//exponent++;
            }
        } else if (exponent_offset.intValue() < 0)
            fraction = fraction.multiply(new BigInteger("2").pow(-exponent_offset.intValue()));

        if (fraction.compareTo(BigInteger.valueOf(0)) == 0) { //fraction == 0
            exponent = BigInteger.valueOf(0);

            // Update flags
            // if the exponent is all 1, than this is either an infinity or a NaN
            if (exponent.compareTo(spec.bias().add(BigInteger.valueOf(1))) == 0) { // exponent == (spec.bias() + 1)
                // Infinity if fraction is all 0
                infinity_flag = (fraction.compareTo(spec.maxFraction().add(BigInteger.valueOf(1))) == 0); //fraction == (spec.maxFraction() + 1)

                // NaN if fraction is anything, except all 0
                NaN_flag = !(fraction.compareTo(spec.maxFraction().add(BigInteger.valueOf(1))) == 0); //fraction == (spec.maxFraction() + 1)
            }
        }
    }

    public void fromDouble(double d) {


        spec.setF(52);
        spec.setE(11);
        assert spec.width() == 64;

        BigInteger i = BigInteger.valueOf(Double.doubleToLongBits(d));


        unpack(i);
    }
    public double toDouble() {
        class Union {
            double f;
            long i;
        }

        Union a = new Union();

        if (infinityFlag) {
            if (signFlag)
                return -Double.POSITIVE_INFINITY;
            return Double.POSITIVE_INFINITY;
        }

        if (NaNFlag) {
            if (signFlag)
                return -Double.NaN;
            return Double.NaN;
        }

        BigInteger i = pack();


        //assert i.isUInt64();

        a.i = i.longValue();//i.toUInt64();
        a.f = Double.longBitsToDouble(a.i) ;
        return a.f;
    }
    public void fromFloat(float f) {
        spec.setF(23);
        spec.setE(8);
        assert spec.width() == 32;
        BigInteger i = BigInteger.valueOf(Float.floatToIntBits(f));

        unpack(i);
    }
    public void fromInteger(BigInteger i) {
        NaN_flag = false;
        infinity_flag = false;
        sign_flag = false;
        exponent = BigInteger.valueOf(spec.getF());
        fraction = i;
        align();
    }
}
