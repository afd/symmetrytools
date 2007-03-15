/* This file was generated by SableCC (http://www.sablecc.org/). */

package src.promela.node;

import src.promela.analysis.*;

@SuppressWarnings("nls")
public final class AMtypeModule extends PModule
{
    private PMtype _mtype_;
    private TSeparator _separator_;

    public AMtypeModule()
    {
        // Constructor
    }

    public AMtypeModule(
        @SuppressWarnings("hiding") PMtype _mtype_,
        @SuppressWarnings("hiding") TSeparator _separator_)
    {
        // Constructor
        setMtype(_mtype_);

        setSeparator(_separator_);

    }

    @Override
    public Object clone()
    {
        return new AMtypeModule(
            cloneNode(this._mtype_),
            cloneNode(this._separator_));
    }

    public void apply(Switch sw)
    {
        ((Analysis) sw).caseAMtypeModule(this);
    }

    public PMtype getMtype()
    {
        return this._mtype_;
    }

    public void setMtype(PMtype node)
    {
        if(this._mtype_ != null)
        {
            this._mtype_.parent(null);
        }

        if(node != null)
        {
            if(node.parent() != null)
            {
                node.parent().removeChild(node);
            }

            node.parent(this);
        }

        this._mtype_ = node;
    }

    public TSeparator getSeparator()
    {
        return this._separator_;
    }

    public void setSeparator(TSeparator node)
    {
        if(this._separator_ != null)
        {
            this._separator_.parent(null);
        }

        if(node != null)
        {
            if(node.parent() != null)
            {
                node.parent().removeChild(node);
            }

            node.parent(this);
        }

        this._separator_ = node;
    }

    @Override
    public String toString()
    {
        return ""
            + toString(this._mtype_)
            + toString(this._separator_);
    }

    @Override
    void removeChild(@SuppressWarnings("unused") Node child)
    {
        // Remove child
        if(this._mtype_ == child)
        {
            this._mtype_ = null;
            return;
        }

        if(this._separator_ == child)
        {
            this._separator_ = null;
            return;
        }

        throw new RuntimeException("Not a child.");
    }

    @Override
    void replaceChild(@SuppressWarnings("unused") Node oldChild, @SuppressWarnings("unused") Node newChild)
    {
        // Replace child
        if(this._mtype_ == oldChild)
        {
            setMtype((PMtype) newChild);
            return;
        }

        if(this._separator_ == oldChild)
        {
            setSeparator((TSeparator) newChild);
            return;
        }

        throw new RuntimeException("Not a child.");
    }
}
