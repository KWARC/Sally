package info.kwarc.sally.sharejs.models;

import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;

import com.fasterxml.jackson.annotation.JsonInclude.Include;
import com.fasterxml.jackson.core.JsonGenerationException;
import com.fasterxml.jackson.core.JsonProcessingException;
import com.fasterxml.jackson.core.io.JsonStringEncoder;
import com.fasterxml.jackson.databind.JsonMappingException;
import com.fasterxml.jackson.databind.ObjectMapper;

public class SpreadsheetModel {
	
	public static class Op {
		List<String> p;
		Object oi;
		Object od;
		
		public Op() {
		}
		
		public List<String> getP() {
			return p;
		}
		
		public Op setP(List<String> p, String ...appendStrings) {
			this.p = new ArrayList<String>(p);
			for (String app : appendStrings)
				this.p.add(app);
			return this;
		}
		public Object getOi() {
			return oi;
		}
		public Op setOi(Object oi) {
			this.oi = oi;
			return this;
		}
		public Object getOd() {
			return od;
		}
		public Op setOd(Object od) {
			this.od = od;
			return this;
		}		
	};

	
	public static interface ChangeAcceptor {
		void acceptOp(String op);
	}
	
	public static class ChangeListener {
		List<String> prefix;
		ChangeAcceptor acceptor;
		
		public ChangeListener(ChangeAcceptor acceptor, List<String> prefix, String ...appendPrefixes) {
			this.acceptor = acceptor;
			this.prefix = new ArrayList<String>(prefix.size()+appendPrefixes.length);
			this.prefix.addAll(prefix);
			for (String p : appendPrefixes) {
				this.prefix.add(p);
			}
		}
		
		public List<String> getPrefix() {
			return prefix;
		}
		
		public ChangeAcceptor getAcceptor() {
			return acceptor;
		}
		
	}
	
	public static class Cell {
		String value;
		String formula;
		
		public String getValue() {
			return value;
		}
		
		public String getFormula() {
			return formula;
		}
		
		public Cell setFormula(String formula) {
			this.formula = formula;
			return this;
		}
		
		public Cell setValue(String value) {
			this.value = value;
			return this;
		}
	}
	
	public static class Sheet {
		
		HashMap<Integer, HashMap<Integer, Cell>> cells;
		ChangeListener listener;
		
		
		public HashMap<Integer, HashMap<Integer, Cell>> getCells() {
			return cells;
		}
		
		public Sheet() {
			cells = new HashMap<Integer, HashMap<Integer,Cell>>();
		}
		
		public void setChangeListener(ChangeListener listener) {
			this.listener = listener;
		}
		
		public Sheet setContent(int row, int col, Cell cell) {
			if (!cells.containsKey(row)) {
				cells.put(row, new HashMap<Integer, Cell>());
			}
			HashMap<Integer, Cell> _row = cells.get(row);
			_row.put(col, cell);
			return this;
		}
	}
	
	HashMap<String, Sheet> sheets;
	ChangeListener listener;
	ObjectMapper mapper; 
	JsonStringEncoder encoder;
	
	public final HashMap<String, Sheet> getSheets() {
		return sheets;
	}
	
	public SpreadsheetModel() {
		sheets = new HashMap<String, SpreadsheetModel.Sheet>();
		listener = null;
		mapper = new ObjectMapper();
		mapper.setSerializationInclusion(Include.NON_NULL);
		encoder = new JsonStringEncoder();
	}

	public Sheet addSheet(String newSheet) {
		Sheet s = new Sheet();
		sheets.put(newSheet, s);
		if (listener != null) {
			try {
				HashMap<String, Sheet> q = new HashMap<String, SpreadsheetModel.Sheet>();
				q.put(newSheet, s);
				listener.getAcceptor().acceptOp(mapper.writeValueAsString(new Op().setP(listener.prefix, "sheets").setOi(q)));
			} catch (JsonProcessingException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
		}
		return s;
	}
	
	public void setChangeListener(ChangeListener listener) {
		this.listener = listener;
		for (String s : sheets.keySet()) {
			sheets.get(s).setChangeListener(new ChangeListener(listener.getAcceptor(), listener.getPrefix(),"sheets", s));
		}
	}
	
	public static void main(String[] args) {
		SpreadsheetModel q = new SpreadsheetModel();
		q.addSheet("Vendor A")
			.setContent(1, 1, new Cell().setValue("11"))
			.setContent(1, 2, new Cell().setValue("12").setFormula("=12"));
		
		ObjectMapper mapper = new ObjectMapper(); // create once, reuse
		try {
			mapper.writeValue(System.out, q);
		} catch (JsonGenerationException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} catch (JsonMappingException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
	}
}
