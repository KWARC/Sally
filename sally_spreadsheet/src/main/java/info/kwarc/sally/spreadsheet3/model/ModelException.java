package info.kwarc.sally.spreadsheet3.model;

public class ModelException extends Exception {

	public ModelException() {}

	public ModelException(String message) {
		super(message);
	}

	public ModelException(Throwable cause) {
		super(cause);
	}

	public ModelException(String message, Throwable cause) {
		super(message, cause);
	}

	public ModelException(String message, Throwable cause,
			boolean enableSuppression, boolean writableStackTrace) {
		super(message, cause, enableSuppression, writableStackTrace);
	}

}
