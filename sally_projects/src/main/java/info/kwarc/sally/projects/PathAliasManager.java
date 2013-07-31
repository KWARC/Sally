package info.kwarc.sally.projects;

import info.kwarc.sally.core.SallyInteractionResultAcceptor;
import info.kwarc.sally.core.SallyContext;
import info.kwarc.sally.core.SallyService;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.Map;

import sally.ScreenCoordinates;
import sally.TheoOpenWindow;

public class PathAliasManager {
	Map<String, String> aliases;
	
	public PathAliasManager() {
		aliases = new HashMap<String, String>();
	}

	public void addPrefix(String prefix, String path) {
		aliases.put(prefix, path);
	}
	
	static boolean done = false;
	
	@SallyService(channel="/alias/set")
	public void setAliases(ArrayList<String> newAliases, SallyInteractionResultAcceptor acceptor, SallyContext context) {
		aliases.clear();
		for (String alias : newAliases) {
			String [] t = alias.split("@");
			aliases.put(t[0], t[1]);
		}
	}
	
	@SallyService(channel="/alias/list")
	public void getAliases(String op, SallyInteractionResultAcceptor acceptor, SallyContext context) {
		if ("get".equals(op)) {
			for (String prefix : aliases.keySet()) {
				acceptor.acceptResult(prefix+"@"+aliases.get(prefix));
			}
		}
	}
	
	@SallyService(channel="/alias/resolve")
	public void resolve(String prefix, SallyInteractionResultAcceptor acceptor, SallyContext context) {
		if (aliases.containsKey(prefix)) {
			acceptor.acceptResult(aliases.get(prefix));
			return;
		}
		aliases.put(prefix, "NA");
		TheoOpenWindow wnd = TheoOpenWindow.newBuilder().setTitle("Alias Manager")
				.setSizeX(400).setSizeY(300).setPosition(ScreenCoordinates.newBuilder().setX(300).setY(300))
				.setUrl("http://localhost:8080/aliasmanager").build();
		context.setContextVar("msg", "Alias path '"+prefix+"' is now known. Please use the form below to define it.");
		Integer wndID = context.getCurrentInteraction().getOneInteraction(wnd, Integer.class);
	}

}
