package info.kwarc.sally.jedit;

import info.kwarc.sally.sharejs.ShareJS;
import info.kwarc.sally.sharejs.TextSnapshot;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;

import org.gjt.sp.jedit.Buffer;
import org.gjt.sp.jedit.EBMessage;
import org.gjt.sp.jedit.EBPlugin;
import org.gjt.sp.jedit.jEdit;
import org.gjt.sp.jedit.buffer.BufferListener;
import org.gjt.sp.jedit.buffer.JEditBuffer;

public class SallyPlugin extends EBPlugin {
	String collection = "users";
	ShareJS sharejs;
	HashMap<String, TextSnapshot> snapshots;
	List<ITextBufferAdapter> adapters;

	public SallyPlugin() {
		sharejs = new ShareJS("http://localhost:7007");
		snapshots = new HashMap<String, TextSnapshot>();
		adapters = new ArrayList<SallyPlugin.ITextBufferAdapter>();
	}

	@Override
	public void handleMessage(EBMessage arg0) {
		super.handleMessage(arg0);
	}

	class ITextBufferAdapter implements BufferListener {
		Buffer origBuffer;

		public ITextBufferAdapter(Buffer buffer) {
			this.origBuffer = buffer;
			buffer.addBufferListener(this);
		}

		public void remove() {
			origBuffer.removeBufferListener(this);
		}

		public void bufferLoaded(JEditBuffer arg0) {
		}

		TextSnapshot getShareSnapshot(Buffer buffer) {
			String file = buffer.getPath();
			if (snapshots.containsKey(file)) {
				return snapshots.get(file);
			}
			if (sharejs.existFile(collection, file)) {
				sharejs.deleteFile(collection, file);
			}
			TextSnapshot snap = TextSnapshot.create(sharejs, collection, file, buffer.getText());
			snapshots.put(file, snap);

			return snap;
		}

		public void contentInserted(JEditBuffer buffer, int startLine, int offset,
				int numLines, int length) {
			buffer.writeLock();
			String textInserted = buffer.getText(offset, length);

			TextSnapshot snapshot = getShareSnapshot((Buffer)buffer);
			snapshot.insertText(offset, textInserted);
			buffer.writeUnlock();
		}

		public void contentRemoved(JEditBuffer buffer, int startLine,
				int offset, int numLines, int length) {
			buffer.writeLock();

			TextSnapshot snapshot = getShareSnapshot((Buffer)buffer);
			snapshot.removeText(offset, length);
			buffer.writeUnlock();

		}

		public void foldHandlerChanged(JEditBuffer arg0) { }

		public void foldLevelChanged(JEditBuffer arg0, int arg1, int arg2) { }

		public void preContentInserted(JEditBuffer arg0, int arg1, int arg2,
				int arg3, int arg4) { }

		public void preContentRemoved(JEditBuffer arg0, int arg1, int arg2,
				int arg3, int arg4) { }

		public void transactionComplete(JEditBuffer arg0) { }

	}

	@Override
	public void start() {
		super.start();
		for (Buffer buf : jEdit.getBuffers()) {
			if (buf.isNewFile()) {
				return;
			}
			adapters.add( new ITextBufferAdapter(buf));			
		}
	}

	@Override
	public void stop() {
		for (ITextBufferAdapter adapt : adapters) {
			adapt.remove();
		}
		adapters.clear();
		snapshots.clear();
		super.stop();
	}
}