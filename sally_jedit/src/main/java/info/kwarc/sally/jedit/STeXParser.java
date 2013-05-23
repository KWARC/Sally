package info.kwarc.sally.jedit;

import java.util.List;

import org.gjt.sp.jedit.Buffer;
import org.gjt.sp.jedit.EditPane;
import org.gjt.sp.util.Log;

import sally.FileRef;
import sally.TextAutocomplete;
import sidekick.SideKickCompletion;
import sidekick.SideKickParsedData;
import sidekick.SideKickParser;
import errorlist.DefaultErrorSource;

public class STeXParser extends SideKickParser {

	public STeXParser() {
		super("stex");
	}

	@Override
	public SideKickParsedData parse(Buffer doc, DefaultErrorSource err) {
		SideKickParsedData result = new SideKickParsedData(doc.getName());
		return result;
	}
	
	@Override
	public SideKickCompletion complete(EditPane pane, int offset) {
		FileRef f = FileRef.newBuilder().setMime("text/stex").setResourceURI("file://"+pane.getBuffer().getPath()).build();
		
		TextAutocomplete auto = TextAutocomplete.newBuilder().setFile(f)
				.setOffset(offset).build();

		Log.log(Log.DEBUG, this, "Starting autocompleting "+auto);
		
		final List<String> results = SallyPlugin.getInteraction().getPossibleInteractions("/autocomplete", auto, String.class);
		Log.log(Log.DEBUG, this, "Got "+results.size()+" results");
		SideKickCompletion completion = new SideKickCompletion(pane.getView(), "blah", results) {
			@Override
			public Object get(int index) {
				return results.get(index);
			}
			
			@Override
			public void insert(int index) {
				super.insert(index);
			}
			
			@Override
			public int size() {
				return results.size();
			}
		};
		return completion;
	}
}
