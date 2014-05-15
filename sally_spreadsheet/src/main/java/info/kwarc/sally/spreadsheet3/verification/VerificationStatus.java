package info.kwarc.sally.spreadsheet3.verification;

/**
 * A class that should be returned by a verification task.
 * Depending on the verification task either sat or unsat can be the desired result.
 * Therefore a VerificationStatus should be returned instead of sat or unsat whereby VERIFIED represents the desired result.
 * @author cliguda
 *
 */
public enum VerificationStatus {
	VERIFIED, FAILED, ERROR
}