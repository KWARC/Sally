package info.kwarc.references;


public interface ReferenceProvider {
	void provide(String format, String contents, IReferenceAcceptor acceptor);
}
