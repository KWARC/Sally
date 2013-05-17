package info.kwarc.sally.jedit;

import info.kwarc.sally.core.SallyActionAcceptor;
import info.kwarc.sally.core.SallyContext;
import info.kwarc.sally.core.SallyService;
import info.kwarc.sally.core.comm.SallyMenuItem;

public class ProjectService {

	public ProjectService() {
	}
	
	@SallyService(channel="/config")
	public void configure(String op, SallyActionAcceptor acceptor, SallyContext context) {
		//SallyInteraction interaction = context.getCurrentInteraction();
		if (op.equals("get")) {
			acceptor.acceptResult(new SallyMenuItem("Configure", "Project") {
				@Override
				public void run() {
					System.out.println("Will configure project");
				}
			});
		}
	}
	
}
