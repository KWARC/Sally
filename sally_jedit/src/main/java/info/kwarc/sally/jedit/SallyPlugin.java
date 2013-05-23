package info.kwarc.sally.jedit;

import info.kwarc.sally.core.SallyInteraction;
import info.kwarc.sally.core.comm.SallyMenuItem;
import info.kwarc.sally.projects.STexParser;
import info.kwarc.sally.projects.PathAliasManager;
import info.kwarc.sally.projects.Project;
import info.kwarc.sally.projects.TeXSelector;
import info.kwarc.sally.theofx.TheoService;

import java.util.ArrayList;
import java.util.List;

import marker.FileMarker;
import marker.MarkerSetsPlugin;

import org.gjt.sp.jedit.Buffer;
import org.gjt.sp.jedit.EBMessage;
import org.gjt.sp.jedit.EBPlugin;
import org.gjt.sp.jedit.jEdit;
import org.gjt.sp.jedit.buffer.BufferListener;
import org.gjt.sp.jedit.buffer.JEditBuffer;

public class SallyPlugin extends EBPlugin {
	static SallyInteraction interaction;
	
	public static SallyInteraction getInteraction() {
		return interaction;
	}
	
	public SallyPlugin() {
		interaction = new SallyInteraction();
		//this.interaction.registerServices(new ReferencingService());
		//this.interaction.registerServices(new SVNService());

		interaction.registerServices(new Project("/home/costea/kwarc/stc/sissi"));
		interaction.registerServices(new TheoService());
		Project serv = new Project("/home/costea/kwarc/stc");
		
		STexParser mmt = new STexParser();
		PathAliasManager alias = new PathAliasManager();
		alias.addPrefix("SiSsI", "file:///home/costea/kwarc/stc/sissi");
		alias.addPrefix("KWARCslides", "file:///home/costea/kwarc/stc/slides");

		interaction.registerServices(serv);
		interaction.registerServices(mmt);
		interaction.registerServices(new TheoService());
		interaction.registerServices(alias);
		//mmt.doIndex(interaction, new TeXSelector());
	}
	
	@Override
	public void handleMessage(EBMessage arg0) {
		super.handleMessage(arg0);
	}
	
	class ITextBufferAdapter implements ITextBuffer, BufferListener {
		Buffer buffer;
		List<Runnable> changeListeners;
		
		public ITextBufferAdapter(Buffer buffer) {
			this.buffer = buffer;
			this.changeListeners = new ArrayList<Runnable>();
			buffer.addBufferListener(this);
		}
		
		void notifyOnChange() {
			for (Runnable r : changeListeners) 
				r.run();
		}
		
		public void addMarker(int line, String text) {
			MarkerSetsPlugin.getActiveMarkerSet().add(new FileMarker(getPath(), line, text));
			List<SallyMenuItem> items = interaction.getPossibleInteractions("/config", "get", SallyMenuItem.class);
			System.out.println("items "+items.size());
			SallyMenuItem chosen = interaction.getOneInteraction(items, SallyMenuItem.class);
			System.out.println("chosen =");
			chosen.run();
		}

		public String getPath() {
			return buffer.getPath();
		}

		public String getText() {
			return buffer.getText();
		}

		public void bufferLoaded(JEditBuffer arg0) {
			notifyOnChange();
		}

		public void contentInserted(JEditBuffer arg0, int arg1, int arg2,
				int arg3, int arg4) {
			notifyOnChange();
		}

		public void contentRemoved(JEditBuffer arg0, int arg1, int arg2,
				int arg3, int arg4) {
			notifyOnChange();
		}

		public void foldHandlerChanged(JEditBuffer arg0) { }

		public void foldLevelChanged(JEditBuffer arg0, int arg1, int arg2) { }

		public void preContentInserted(JEditBuffer arg0, int arg1, int arg2,
				int arg3, int arg4) { }

		public void preContentRemoved(JEditBuffer arg0, int arg1, int arg2,
				int arg3, int arg4) { }

		public void transactionComplete(JEditBuffer arg0) { }

		public void addOnChangeListener(Runnable runnable) {
			changeListeners.add(runnable);
		}

		public void removeAllMarkers() {
			for (FileMarker f : MarkerSetsPlugin.getActiveMarkerSet().getMarkersFor(buffer.getPath())) {
				MarkerSetsPlugin.getActiveMarkerSet().remove(f);
			}
		}
	}
	
	@Override
	public void start() {
		super.start();
		for (Buffer buf : jEdit.getBuffers()) {
			if (buf.isNewFile()) {
				return;
			}
			
			
			interaction.registerServices(new SallyJEditService(new ITextBufferAdapter(buf), interaction));
		}
	}

	@Override
	public void stop() {
		super.stop();
	}
}