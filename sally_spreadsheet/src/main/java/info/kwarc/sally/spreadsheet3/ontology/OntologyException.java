package info.kwarc.sally.spreadsheet3.ontology;

public class OntologyException extends Exception {

	private static final long serialVersionUID = 1L;

	public OntologyException() {}

	public OntologyException(String message) {
		super(message);
	}

	public OntologyException(Throwable cause) {
		super(cause);
	}

	public OntologyException(String message, Throwable cause) {
		super(message, cause);
	}

	public OntologyException(String message, Throwable cause,
			boolean enableSuppression, boolean writableStackTrace) {
		super(message, cause, enableSuppression, writableStackTrace);
	}

}
