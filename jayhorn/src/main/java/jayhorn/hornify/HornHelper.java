package jayhorn.hornify;

import java.util.Collections;
import java.util.Comparator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import jayhorn.hornify.encoder.ExpressionEncoder;
import jayhorn.solver.*;
import soottocfg.cfg.type.*;
import soottocfg.cfg.type.BoolType;
import soottocfg.cfg.type.IntType;
import soottocfg.cfg.variable.Variable;
import soottocfg.soot.SootToCfg;

public class HornHelper {

	public static final int NullValue = 0;
	
	private static HornHelper hh;

	private ProverADT stringADT;

	private ProverADT singleFloatingPointADT;

	private ProverADT doubleFloatingPointADT;

	private ProverADT singleTempFloatingPointADT;

	private ProverADT doubleTempFloatingPointADT;

	private ProverADT singleTempFloatingPointOperandsADT;

	private ProverADT doubleTempFloatingPointOperandsADT;

	private ProverFun xOrSingleSigns;

	private ProverFun xOrDoubleSigns;

	private ProverFun isOVFSingleExp;

	private ProverFun isUDFSingleExp;

	private ProverFun isUDFDoubleExp;

	private ProverFun isOVFDoubleExp;

	private ProverFun isOVFSingleSigInAdd;
	private ProverFun isOVFSingleSigInMul;

	private ProverFun isOVFDoubleSigInAdd;
	private ProverFun isOVFDoubleSigInMul;

	private ProverFun extractSingleSigLSBInMul;

	private ProverFun extractSingleSigGInMul;

	private ProverFun extractSingleSigRInMul;

	private ProverFun computeSingleSigStickyInMul;

	private ProverFun extractDoubleSigLSBInMul;

	private ProverFun extractDoubleSigGInMul;

	private ProverFun extractDoubleSigRInMul;

	private ProverFun computeDoubleSigStickyInMul;

    private ProverFun requiredRoundingUp;

	private  ProverFun roundUpSingleSigInMul;
	private  ProverFun roundUpDoubleSigInMul;

	private ProverFun makeSingleOVFFun;
	private ProverFun makeDoubleOVFFun;

	private ProverFun makeSingleUDFFun;

	private ProverFun makeDoubleUDFFun;

	private ProverFun existSingleZeroFun;
	private ProverFun existDoubleZeroFun;
	private ProverFun existSingleInfFun;
	private ProverFun existDoubleInfFun;
	private ProverFun existSingleNaNFun;
	private ProverFun existDoubleNaNFun;
	private ProverFun singleOperandsEqInfFun;
	private ProverFun doubleOperandsEqInfFun;
	private ProverFun singleOperandsEqZeroFun;
	private ProverFun doubleOperandsEqZeroFun;
	private ProverFun isSingleNegFun;
	private ProverFun isDoubleNegFun;
	private ProverFun areEqSingleSignsFun;
	private ProverFun areEqDoubleSignsFun;

	private ProverFun isSingleInf;
	private ProverFun isDoubleInf;
	private ProverFun isSingleNaN;
	private ProverFun isDoubleNaN;

	private ProverFun makeSingleNaN;

	private ProverFun makeDoubleNaN;

	private ProverFun negateSingleFun;
	private ProverFun negateDoubleFun;
	private ProverFun makeSingleInfFun;
	private ProverFun makeDoubleInfFun;

	private ProverFun existSpecCasForSingleInMul;
	private ProverFun existSpecCasForDoubleInMul;
	private ProverFun needsNormalizationInSingleDiv;
	private ProverFun subSingleExponentsInDiv;
	private ProverFun divSingleSigs;
	private ProverFun normalizeSingleExSigInDiv;
	private ProverFun roundingUpInSingleDiv;
	private ProverFun extractLSBInSingleDivResult;
	private ProverFun extractGInSingleDivResult;
	private ProverFun extractRInSingleDivResult;
	private ProverFun computeSInSingleDivResult;

	private ProverFun needsNormalizationInDoubleDiv;
	private ProverFun subDoubleExponentsInDiv;
	private ProverFun divDoubleSigs;
	private ProverFun normalizeDoubleExSigInDiv;
	private ProverFun roundingUpInDoubleDiv;
	private ProverFun extractLSBInDoubleDivResult;
	private ProverFun extractGInDoubleDivResult;
	private ProverFun extractRInDoubleDivResult;
	private ProverFun computeSInDoubleDivResult;

	
	public static void resetInstance() {
		hh = null;
	}

	public static HornHelper hh() {
		if (null == hh) {
			hh = new HornHelper();
		}
		return hh;
	}

	private HornHelper() {
	}

	public void setStringADT(ProverADT stringADT) {
		this.stringADT = stringADT;
	}
	public void setSingleFloatingPointADT(ProverADT singleFloatingPointADT) {
		this.singleFloatingPointADT = singleFloatingPointADT;
	}
	public void setDoubleFloatingPointADT(ProverADT doubleFloatingPointADT) {
		this.doubleFloatingPointADT = doubleFloatingPointADT;
	}
	public void setSingleTempFloatingPointADT(ProverADT singleTempFloatingPointADT) {
		this.singleTempFloatingPointADT = singleTempFloatingPointADT;
	}
	public void setDoubleTempFloatingPointADT(ProverADT doubleTempFloatingPointADT) {
		this.doubleTempFloatingPointADT = doubleTempFloatingPointADT;
	}
	public void setSingleTempFloatingOperandsPointADT(ProverADT singleTempFloatingPointOperandsADT) {
		this.singleTempFloatingPointOperandsADT = singleTempFloatingPointOperandsADT;
	}
	public void setDoubleTempFloatingPointOperandsADT(ProverADT doubleTempFloatingPointOperandsADT) {
		this.doubleTempFloatingPointOperandsADT = doubleTempFloatingPointOperandsADT;
	}
	public void setxOrSingleSigns(ProverFun xOrSingleSigns)
	{
		this.xOrSingleSigns = xOrSingleSigns;
	}
	public void setxOrDoubleSigns(ProverFun xOrDoubleSigns)
	{
		this.xOrDoubleSigns = xOrDoubleSigns;
	}
	public void  setIsOVFSingleExp(ProverFun isOVFSingleExp)
	{
		this.isOVFSingleExp = isOVFSingleExp;
	}
	public void  setIsUDFSingleExp(ProverFun isUDFSingleExp)
	{
		this.isUDFSingleExp = isUDFSingleExp;
	}
	public void  setIsOVFDoubleExp(ProverFun isOVFDoubleExp)
	{
		this.isOVFDoubleExp = isOVFDoubleExp;
	}
	public void setIsUDFDoubleExp(ProverFun isUDFDoubleExp)
	{
		this.isUDFDoubleExp = isUDFDoubleExp;
	}

	public void  setIsOVFSingleSigInAdd(ProverFun isOVFSingleSigInAdd)
	{
		this.isOVFSingleSigInAdd = isOVFSingleSigInAdd;
	}
	public void  setIsOVFSingleSigInMul(ProverFun isOVFSingleSigInMul)
	{
		this.isOVFSingleSigInMul = isOVFSingleSigInMul;
	}
	public void  setIsOVFDoubleSigInAdd(ProverFun isOVFDoubleSigInAdd)
	{
		this.isOVFDoubleSigInAdd = isOVFDoubleSigInAdd;
	}
	public void  setIsOVFDoubleSigInMul(ProverFun isOVFDoubleSigInMul)
	{
		this.isOVFDoubleSigInMul = isOVFDoubleSigInMul;
	}
	public void setExtractSingleSigLSBInMul(ProverFun extractSingleSigLSBInMul)
	{
		this.extractSingleSigLSBInMul = extractSingleSigLSBInMul;
	}
	public void setExtractSingleSigGInMul(ProverFun extractSingleSigGInMul)
	{
		this.extractSingleSigGInMul = extractSingleSigGInMul;
	}
	public void setExtractSingleSigRInMul(ProverFun extractSingleSigRInMul)
	{
		this.extractSingleSigRInMul = extractSingleSigRInMul;
	}
	public void setComputeSingleSigStickyInMul(ProverFun computeSingleSigStickyInMul)
	{
		this.computeSingleSigStickyInMul = computeSingleSigStickyInMul;
	}
	public void setExtractDoubleSigLSBInMul(ProverFun extractDoubleSigLSBInMul)
	{
		this.extractDoubleSigLSBInMul = extractDoubleSigLSBInMul;
	}

	public void setExtractDoubleSigGInMul(ProverFun extractDoubleSigGInMul)
	{
		this.extractDoubleSigGInMul = extractDoubleSigGInMul;
	}
	public void setExtractDoubleSigRInMul(ProverFun extractDoubleSigRInMul)
	{
		this.extractDoubleSigRInMul = extractDoubleSigRInMul;
	}
	public void setComputeDoubleSigStickyInMul(ProverFun computeDoubleSigStickyInMul)
	{
		this.computeDoubleSigStickyInMul = computeDoubleSigStickyInMul;
	}
	public void  setRequiredRoundingUp(ProverFun requiredRoundingUp)
	{
		this.requiredRoundingUp = requiredRoundingUp;
	}
	public void setRoundUpSingleSigInMul(ProverFun roundUpSingleSigInMul)
	{
		this.roundUpSingleSigInMul = roundUpSingleSigInMul;
	}
	public void setRoundUpDoubleSigInMul(ProverFun roundUpDoubleSigInMul)
	{
		this.roundUpDoubleSigInMul = roundUpDoubleSigInMul;
	}
	public void  setMakeSingleOVFFun(ProverFun makeSingleOVFFun)
	{
		this.makeSingleOVFFun = makeSingleOVFFun;
	}
	public void setMakeDoubleOVFFun(ProverFun makeDoubleOVFFun)
	{
		this.makeDoubleOVFFun = makeDoubleOVFFun;
	}
	public void setMakeSingleUDFFun(ProverFun makeSingleUDFFun)
	{
		this.makeSingleUDFFun = makeSingleUDFFun;
	}
	public void setMakeDoubleUDFFun(ProverFun makeDoubleUDFFun)
	{
		this.makeDoubleUDFFun = makeDoubleUDFFun;
	}
	public void setExistSingleZeroFun(ProverFun existSingleZeroFun)
	{
		this.existSingleZeroFun = existSingleZeroFun;
	}
	public void setExistDoubleZeroFun(ProverFun existDoubleZeroFun)
	{
		this.existDoubleZeroFun = existDoubleZeroFun;
	}
	public void setExistSingleInfFun(ProverFun existSingleInfFun)
	{
		this.existSingleInfFun = existSingleInfFun;
	}
	public void  setExistDoubleInfFun(ProverFun existDoubleInfFun)
	{
		this.existDoubleInfFun = existDoubleInfFun;
	}
	public void setExistSingleNaNFun(ProverFun existSingleNaNFun)
	{
		this.existSingleNaNFun = existSingleNaNFun;
	}
	public void setExistDoubleNaNFun(ProverFun existDoubleNaNFun)
	{
		this.existDoubleNaNFun = existDoubleNaNFun;
	}
	public void setSingleOperandsEqInfFun(ProverFun singleOperandsEqInfFun)
	{
		this.singleOperandsEqInfFun = singleOperandsEqInfFun;
	}
	public void setSingleOperandsEqZeroFun(ProverFun singleOperandsEqZeroFun)
	{
		this.singleOperandsEqZeroFun = singleOperandsEqZeroFun;
	}
	public void setIsSingleNegFun(ProverFun isSingleNegFun)
	{
		this.isSingleNegFun = isSingleNegFun;
	}
	public void setAreEqSingleSignsFun(ProverFun areEqSingleSignsFun)
	{
		this.areEqSingleSignsFun = areEqSingleSignsFun;
	}
	public void setDoubleOperandsEqInfFun(ProverFun doubleOperandsEqInfFun)
	{
		this.doubleOperandsEqInfFun = doubleOperandsEqInfFun;
	}
	public void setDoubleOperandsEqZeroFun(ProverFun doubleOperandsEqZeroFun)
	{
		this.doubleOperandsEqZeroFun = doubleOperandsEqZeroFun;
	}
	public void setIsDoubleNegFun(ProverFun isDoubleNegFun)
	{
		this.isDoubleNegFun = isDoubleNegFun;
	}
	public void setAreEqDoubleSignsFun(ProverFun areEqDoubleSignsFun)
	{
		this.areEqDoubleSignsFun = areEqDoubleSignsFun;
	}
	public void setIsSingleNaN(ProverFun isSingleNaN)
	{
		this.isSingleNaN = isSingleNaN;
	}
	public void setIsSingleInf(ProverFun isSingleInf)
	{
		this.isSingleInf = isSingleInf;
	}
	public void setIsDoubleNaN(ProverFun isDoubleNaN)
	{
		this.isDoubleNaN = isDoubleNaN;
	}
	public void setIsDoubleInf(ProverFun isDoubleInf)
	{
		this.isDoubleInf = isDoubleInf;
	}
	public void setMakeSingleNaN(ProverFun makeSingleNaN)
	{
		this.makeSingleNaN = makeSingleNaN;
	}
	public void setMakeDoubleNaN(ProverFun makeDoubleNaN)
	{
		this.makeDoubleNaN = makeDoubleNaN;
	}
	public void setNegateSingleFun(ProverFun negateSingleFun)
	{
		this.negateSingleFun = negateSingleFun;
	}
	public void setNegateDoubleFun(ProverFun negateDoubleFun)
	{
		this.negateDoubleFun = negateDoubleFun;
	}
	public void setMakeSingleInfFun(ProverFun makeSingleInfFun)
	{
		this.makeSingleInfFun = makeSingleInfFun;
	}
	public void setMakeDoubleInfFun(ProverFun makeDoubleInfFun)
	{
		this.makeDoubleInfFun = makeDoubleInfFun;
	}
	public void setExistSpecCasForSingleInMul(ProverFun existSpecCasForSingleInMul)
	{
		this.existSpecCasForSingleInMul = existSpecCasForSingleInMul;
	}
	public void setExistSpecCasForDoubleInMul(ProverFun existSpecCasForDoubleInMul)
	{
		this.existSpecCasForDoubleInMul = existSpecCasForDoubleInMul;
	}
	public void setNeedsNormalizationInSingleDiv(ProverFun needsNormalizationInSingleDiv)
	{
		this.needsNormalizationInSingleDiv = needsNormalizationInSingleDiv;
	}
	public void setNormalizeSingleExSigInDiv(ProverFun normalizeSingleExSigInDiv)
	{
		this.normalizeSingleExSigInDiv = normalizeSingleExSigInDiv;
	}
	public void  setDivSingleSigs(ProverFun divSingleSigs)
	{
		this.divSingleSigs = divSingleSigs;
	}
	public void setSubSingleExponentsInDiv(ProverFun subSingleExponentsInDiv)
	{
		this.subSingleExponentsInDiv = subSingleExponentsInDiv;
	}
	public void setRoundingUpInSingleDiv(ProverFun roundingUpInSingleDiv)
	{
		this.roundingUpInSingleDiv = roundingUpInSingleDiv;
	}
	public  void setExtractLSBInSingleDivResult(ProverFun extractLSBInSingleDivResult)
	{
		this.extractLSBInSingleDivResult = extractLSBInSingleDivResult;
	}
	public void setExtractGInSingleDivResult(ProverFun extractGInSingleDivResult)
	{
		this.extractGInSingleDivResult = extractGInSingleDivResult;
	}
	public void setExtractRInSingleDivResult(ProverFun extractRInSingleDivResult)
	{
		this.extractRInSingleDivResult = extractRInSingleDivResult;
	}
	public void setComputeSInSingleDivResult(ProverFun computeSInSingleDivResult)
	{
		this.computeSInSingleDivResult = computeSInSingleDivResult;
	}
	public void setNeedsNormalizationInDoubleDiv(ProverFun needsNormalizationInDoubleDiv)
	{
		this.needsNormalizationInDoubleDiv = needsNormalizationInDoubleDiv;
	}
	public void setDivDoubleSigs(ProverFun divDoubleSigs)
	{
		this.divDoubleSigs = divDoubleSigs;
	}
	public void setSubDoubleExponentsInDiv(ProverFun subDoubleExponentsInDiv)
	{
		this.subDoubleExponentsInDiv = subDoubleExponentsInDiv;
	}
	public void setNormalizeDoubleExSigInDiv(ProverFun normalizeDoubleExSigInDiv)
	{
		this.normalizeDoubleExSigInDiv = normalizeDoubleExSigInDiv;
	}
	public void setRoundingUpInDoubleDiv(ProverFun roundingUpInDoubleDiv)
	{
		this.roundingUpInDoubleDiv = roundingUpInDoubleDiv;
	}
	public void  setExtractLSBInDoubleDivResult(ProverFun extractLSBInDoubleDivResult)
	{
		this.extractLSBInDoubleDivResult = extractLSBInDoubleDivResult;
	}
	public void setExtractGInDoubleDivResult(ProverFun extractGInDoubleDivResult)
	{
		this.extractGInDoubleDivResult = extractGInDoubleDivResult;
	}
	public void setExtractRInDoubleDivResult(ProverFun extractRInDoubleDivResult)
	{
		this.extractRInDoubleDivResult = extractRInDoubleDivResult;
	}
	public void setComputeSInDoubleDivResult(ProverFun computeSInDoubleDivResult)
	{
		this.computeSInDoubleDivResult = computeSInDoubleDivResult;
	}

	public ProverADT getStringADT() {
		return stringADT;
	}

	public ProverADT getSingleFloatingPointADT() {
		return singleFloatingPointADT;
	}

	public ProverADT getDoubleFloatingPointADT() {
		return doubleFloatingPointADT;
	}

	public ProverADT getSingleTempFloatingPointADT() {
		return singleTempFloatingPointADT;
	}

	public ProverADT getDoubleTempFloatingPointADT() {
		return doubleTempFloatingPointADT;
	}

	public ProverADT getSingleTempFloatingPointOperandsADT() {
		return singleTempFloatingPointOperandsADT;
	}

	public ProverADT getDoubleTempFloatingPointOperandsADT() {
		return doubleTempFloatingPointOperandsADT;
	}

	public ProverFun getxOrSingleSigns(){return xOrSingleSigns;}

	public ProverFun getxOrDoubleSigns(){return xOrDoubleSigns;}

	public ProverFun getIsOVFSingleExp(){return isOVFSingleExp;}
	public ProverFun getIsUDFSingleExp(){return  isUDFSingleExp;}

	public ProverFun getIsOVFDoubleExp(){return isOVFDoubleExp;}
	public ProverFun getIsUDFDoubleExp(){return isUDFDoubleExp;}

    public ProverFun getIsOVFSingleSigInAdd(){return isOVFSingleSigInAdd;}
	public ProverFun getIsOVFSingleSigInMul(){return isOVFSingleSigInMul;}
	public ProverFun getIsOVFDoubleSigInAdd(){return isOVFDoubleSigInAdd;}
	public  ProverFun getIsOVFDoubleSigInMul(){return isOVFDoubleSigInMul;}

	public ProverFun getExtractSingleSigLSBInMul(){return extractSingleSigLSBInMul;}
	public ProverFun getExtractSingleSigGInMul(){return extractSingleSigGInMul;}
	public ProverFun getExtractSingleSigRInMul(){return extractSingleSigRInMul;}

	public ProverFun getComputeSingleSigStickyInMul(){return computeSingleSigStickyInMul;}
	public ProverFun getExtractDoubleSigLSBInMul(){return extractDoubleSigLSBInMul;}
	public ProverFun getExtractDoubleSigGInMul(){return extractDoubleSigGInMul;}
	public ProverFun getExtractDoubleSigRInMul(){return extractDoubleSigRInMul;}

	public ProverFun getComputeDoubleSigStickyInMul(){return computeDoubleSigStickyInMul;}
	public ProverFun getRequiredRoundingUp(){return requiredRoundingUp;}
	public ProverFun getRoundUpSingleSigInMul(){return roundUpSingleSigInMul;}
	public ProverFun getRoundUpDoubleSigInMul(){return roundUpDoubleSigInMul;}
	public ProverFun getMakeSingleOVFFun(){return makeSingleOVFFun;}
	public ProverFun getMakeDoubleOVFFun(){return makeDoubleOVFFun;}
	public ProverFun getMakeSingleUDFFun(){return makeSingleUDFFun;}
	public ProverFun getMakeDoubleUDFFun(){return makeDoubleUDFFun;}
	public ProverFun getExistSingleZeroFun(){return existSingleZeroFun;}
	public ProverFun getExistDoubleZeroFun(){return existDoubleZeroFun;}
	public ProverFun getExistSingleInfFun(){return existSingleInfFun;}
	public ProverFun getExistDoubleInfFun(){return existDoubleInfFun;}
	public ProverFun getExistSingleNaNFun(){return existSingleNaNFun;}
	public ProverFun getExistDoubleNaNFun(){return existDoubleNaNFun;}
	public ProverFun getSingleOperandsEqInfFun(){return singleOperandsEqInfFun;}
	public ProverFun getSingleOperandsEqZeroFun(){return singleOperandsEqZeroFun;}

	public ProverFun getIsSingleNegFun(){return isSingleNegFun;}
	public ProverFun getAreEqSingleSignsFun(){return areEqSingleSignsFun;}
	public ProverFun getDoubleOperandsEqInfFun(){return doubleOperandsEqInfFun;}
	public ProverFun getDoubleOperandsEqZeroFun(){return doubleOperandsEqZeroFun;}
	public ProverFun getIsDoubleNegFun(){return isDoubleNegFun;}
	public ProverFun getAreEqDoubleSignsFun(){return areEqDoubleSignsFun;}
	public ProverFun getIsSingleInf(){return isSingleInf;}
	public ProverFun getIsSingleNaN(){return isSingleNaN;}

	public ProverFun getIsDoubleInf(){return isDoubleInf;}
	public ProverFun getIsDoubleNaN(){return isDoubleNaN;}
	public ProverFun getMakeSingleNaN(){return makeSingleNaN;}
	public ProverFun getMakeDoubleNaN(){return makeDoubleNaN;}
	public ProverFun getNegateSingleFun(){return negateSingleFun;}
	public ProverFun getNegateDoubleFun(){return negateDoubleFun;}

	public ProverFun getMakeSingleInfFun(){return makeSingleInfFun;}
	public ProverFun getMakeDoubleInfFun(){return makeDoubleInfFun;}
	public ProverFun getExistSpecCasForSingleInMul(){return existSpecCasForSingleInMul;}
	public ProverFun getExistSpecCasForDoubleInMul(){return existSpecCasForDoubleInMul;}

	public ProverFun getNeedsNormalizationInSingleDiv(){return needsNormalizationInSingleDiv;}
	public ProverFun getDivSingleSigs(){return divSingleSigs;}
	public ProverFun getSubSingleExponentsInDiv(){return subSingleExponentsInDiv;}
	public  ProverFun getNormalizeSingleExSigInDiv(){return  normalizeSingleExSigInDiv;}
	public ProverFun getRoundingUpInSingleDiv(){return  roundingUpInSingleDiv;}
	public ProverFun getExtractLSBInSingleDivResult(){return extractLSBInSingleDivResult;}
	public ProverFun getExtractGInSingleDivResult(){return extractGInSingleDivResult;}
	public ProverFun getExtractRInSingleDivResult(){return extractRInSingleDivResult;}
	public ProverFun getComputeSInSingleDivResult(){return computeSInSingleDivResult;}
	public ProverFun getNeedsNormalizationInDoubleDiv(){return needsNormalizationInDoubleDiv;}
	public ProverFun getSubDoubleExponentsInDiv(){return subDoubleExponentsInDiv;}
	public ProverFun getDivDoubleSigs(){return divDoubleSigs;}
	public ProverFun getNormalizeDoubleExSigInDiv(){return normalizeDoubleExSigInDiv;}
	public ProverFun getRoundingUpInDoubleDiv(){return roundingUpInDoubleDiv;}
	public ProverFun getExtractLSBInDoubleDivResult(){return extractLSBInDoubleDivResult;}
	public ProverFun getExtractGInDoubleDivResult(){return extractGInDoubleDivResult;}
	public ProverFun getExtractRInDoubleDivResult(){return extractRInDoubleDivResult;}
	public ProverFun getComputeSInDoubleDivResult(){return computeSInDoubleDivResult;}

	/**
	 * Creates a ProverType from a Type.
	 * TODO: not fully implemented.
	 * 
	 * @param p
	 * @param t
	 * @return
	 */
	public ProverType getProverType(Prover p, Type t) {
		if (t == IntType.instance()) {
			return p.getIntType();
		}
		if (t == StringType.instance()) {
			if (stringADT == null)
				throw new RuntimeException("stringADT is not set");
			return stringADT.getType(0);
		}
		if (t == FloatType.instance())
		{
			if(singleFloatingPointADT == null)
				throw new RuntimeException("singleFloatingPointADT is not set");
			return singleFloatingPointADT.getType(0);
		}
		if (t == DoubleType.instance())
		{
			if(doubleFloatingPointADT == null)
				throw new RuntimeException("doubleFloatingPointADT is not set");
			return doubleFloatingPointADT.getType(0);
		}
		if (t == BoolType.instance()) {
			return p.getBooleanType();
		}


		if (t instanceof ReferenceType) {
			ReferenceType rt = (ReferenceType) t;
			final ProverType[] subTypes = new ProverType[rt.getElementTypeList().size()];
			for (int i = 0; i < rt.getElementTypeList().size(); i++) {
				subTypes[i] = getProverType(p, rt.getElementTypeList().get(i));
			}
			return p.getTupleType(subTypes);
		}
		if (t instanceof WrappedProverType)
			return ((WrappedProverType)t).getProverType();
		if (t instanceof TypeType) {
			return p.getIntType();
		}

		throw new IllegalArgumentException("don't know what to do with " + t);
	}
	public ProverType getProverType(Prover p, Type t,int arrity) {
		if(t == Type.instance())
		{
			return p.getBVType(arrity);
		}
		else
			return getProverType(p,t);

	}
	
	public ProverTupleExpr mkNullExpression(Prover p, ProverType[] types, ExpressionEncoder expEncoder) {
		ProverExpr[] subExprs = new ProverExpr[types.length];
		for (int i = 0; i < types.length; i++) {
			if (types[i] instanceof jayhorn.solver.BoolType) {
				subExprs[i] = p.mkLiteral(false);
			} else if (types[i] instanceof jayhorn.solver.IntType) {
				subExprs[i] = p.mkLiteral(NullValue);
			} else if (types[i] instanceof jayhorn.solver.ProverADTType
						&& types[i].toString().equals(StringType.instance().toString())) {	// TODO: better check
				subExprs[i] = expEncoder.getStringEncoder().mkStringPE("");
			} else if (types[i] instanceof jayhorn.solver.ProverADTType
					&& types[i].toString().equals("DoubleFloatingPoint")) {	// TODO: better check
				subExprs[i] = expEncoder.getDoubleFloatingPointEnCoder().mkDoublePE(0.0);
			}
			else if (types[i] instanceof jayhorn.solver.ProverADTType
					&& types[i].toString().equals("FloatingPoint")) {	// TODO: better check
				subExprs[i] = expEncoder.getSingleFloatingPointEnCoder().mkFloatPE(0.0F);
			}
			else if (types[i] instanceof ProverTupleType) {
				subExprs[i] = mkNullExpression(p, ((ProverTupleType)types[i]).getSubTypes(), expEncoder);
			} else {
				throw new RuntimeException("Not implemented " + types[i].getClass());
			}
		}
		return (ProverTupleExpr) p.mkTuple(subExprs);
	}

	public ProverFun genHornPredicate(Prover p, String name, List<Variable> sortedVars) {
		final List<ProverType> types = new LinkedList<ProverType>();
		for (Variable v : sortedVars) {
			if(v.getType() != Type.instance())
				types.add(getProverType(p, v.getType()));
			else types.add(getProverType(p, v.getType(),v.getArrity()));


		}
		return p.mkHornPredicate(name, types.toArray(new ProverType[types.size()]));
	}

	private int varNum = 0;

	public int newVarNum() {
		return varNum++;
	}

        /**
         * Apply a substitution to the values of a variable map. This will only
         * check for complete matches, i.e., it won't substitute any sub-expressions
         */
        public void substitute(Map<Variable, ProverExpr> varMap,
                               Map<ProverExpr, ProverExpr> subst) {
            for (Map.Entry<Variable, ProverExpr> e : varMap.entrySet())
                if (subst.containsKey(e.getValue()))
                    e.setValue(subst.get(e.getValue()));
        }

	public List<ProverExpr> findOrCreateProverVar(Prover p, List<Variable> cfgVars, Map<Variable, ProverExpr> varMap) {
		List<ProverExpr> res = new LinkedList<ProverExpr>();
		for (Variable v : cfgVars) {
			res.add(findOrCreateProverVar(p, v, varMap));
		}
		return res;
	}

	public ProverExpr findOrCreateProverVar(Prover p, Variable v, Map<Variable, ProverExpr> varMap) {
		if (!varMap.containsKey(v)) {
			varMap.put(v, createVariable(p, v));
		}
		return varMap.get(v);
	}

	public ProverExpr createVariable(Prover p, Variable v) {
		ProverType pt = getProverType(p, v.getType(),v.getArrity());
		return p.mkHornVariable(v.getName() + "_" + newVarNum(), pt);
	}

	public ProverExpr createVariable(Prover p, String prefix, Type tp) {
		return p.mkHornVariable(prefix + newVarNum(), getProverType(p, tp));
	}

	public List<Variable> setToSortedList(Set<Variable> set) {
		List<Variable> res = new LinkedList<Variable>(set);
		if (!res.isEmpty()) {
			Collections.sort(res, new Comparator<Variable>() {
				@Override
				public int compare(final Variable object1, final Variable object2) {
					return object1.getName().compareTo(object2.getName());
				}
			});
		}
		return res;
	}
}
