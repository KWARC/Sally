package info.kwarc.sally.networking.cometd;

import javax.ws.rs.GET;
import javax.ws.rs.Path;

@Path("datalog")
public class CometDLogger {
	@GET
	public String doLog() {
		return "";
	}
}
